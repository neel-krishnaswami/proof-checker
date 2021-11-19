module Seq = struct
  include Seq

  let cons x s = fun () -> Cons(x, s)

  let rec unfold : ('a -> ('b * 'a) option) -> 'a -> 'b t = 
    fun f seed () -> 
      match f seed with
      | None -> Nil
      | Some(x, seed) -> Cons(x, unfold f seed)

  let concat ss = 
    let rec next = function
      | [] -> None
      | s :: ss -> 
         (match s() with
          | Nil -> next ss 
          | Cons(x, s') -> Some(x, s' :: ss))
    in
    unfold next ss 

  let flatten xss = 
    let rec next xss = 
      match xss() with
      | Nil -> None
      | Cons(ys, yss) -> 
             (match ys() with
              | Nil -> next yss
              | Cons(z, zs) -> Some(z, cons zs yss))
    in
    unfold next xss

end


type var = string

type sort  = Nat


(* Terms with hash-consing *)           
module type Term = sig
  type t 

  type 'a tm = 
    | Z 
    | S of 'a
    | V of var
    | Pair of 'a * 'a 
    | Fst of 'a 
    | Snd of 'a 
    | App of 'a * 'a 

  val map : ('a -> 'b) -> 'a tm -> 'b tm 

  val z : t
  val s : t -> t
  val v : var -> t 
  val pair : t -> t -> t 
  val fst : t -> t 
  val snd : t -> t 
  val app : t -> t -> t 

  val into : t tm -> t
  val out : t -> t tm 

  val predecessors : t -> t list

  val compare : t -> t -> int
  val (=) : t -> t -> bool
  val (<) : t -> t -> bool
  val (<=) : t -> t -> bool
end

module Tm : Term = struct
  type t = int
  type 'a tm = 
    | Z 
    | S of 'a
    | V of var
    | Pair of 'a * 'a 
    | Fst of 'a 
    | Snd of 'a 
    | App of 'a * 'a 

  let map f = function 
    | Z -> Z
    | S a -> S (f a)
    | V x -> V x
    | Pair(a, a') -> Pair(f a, f a') 
    | Fst a -> Fst (f a)
    | Snd a -> Snd (f a)
    | App(a, a') -> Pair(f a, f a')

  let children = function
    | Z 
    | V _ -> []
    | S t
    | Fst t 
    | Snd t -> [t]
    | Pair(t1, t2)
    | App(t1, t2) -> [t1; t2]

  let h = Hashtbl.create 0
  let h' = Hashtbl.create 0
  let parents = Hashtbl.create 0 

  let id = ref 0
  let next () = incr id; !id

  let into x = 
    match Hashtbl.find_opt h x with
    | Some id -> id
    | None -> let n = next() in
              Hashtbl.add h x n;
              Hashtbl.add h' n x;
              Hashtbl.add parents n [];
              List.iter 
               (fun n' -> Hashtbl.add parents n' (n :: Hashtbl.find parents n'))
               (children x);
              n 

  let predecessors t = Hashtbl.find parents t 

  let z = into Z
  let s n = into (S n)
  let v x = into (V x)
  let pair t1 t2 = into (Pair(t1, t2))
  let fst t = into (Fst t)
  let snd t = into (Snd t)
  let app t1 t2 = into (Pair(t1, t2))

  let out tm = Hashtbl.find h' tm 


  let compare = Stdlib.compare
  let (=) = Stdlib.(=)
  let (<) = Stdlib.(<)
  let (<=) = Stdlib.(<=)
end

module DisjointSet = struct
  type t = {
      value : Tm.t;
      mutable parent : path; 
      mutable rank : int;
      id : int 
    }
  and path = 
    | Root of Tm.t list 
    | Link of t 

  let id = ref 0 

  let create tm = {value = tm; 
                   parent = Root [tm]; 
                   rank = 0;
                   id = (incr id; !id)}

  let rec find' t = 
    match t.parent with
    | Root ts -> (t, ts)
    | Link t' -> let root, ts = find' t' in
                 t.parent <- Link root;
                 (root, ts)

  let find t = fst (find' t)

  let equiv t = snd (find' t)

  let union t1 t2 = 
    let (t1, ts1) = find' t1 in
    let (t2, ts2) = find' t2 in 
    if not (t1 == t2) then
      (match compare t1.rank t2.rank with
       | -1 -> t1.parent <- Link t2;
               t2.parent <- Root (ts1 @ ts2)
       | 1  -> t2.parent <- Link t1;
               t1.parent <- Root (ts1 @ ts2)
       | 0  -> t1.parent <- Link t2;
               t2.parent <- Root (ts1 @ ts2);
               t2.rank <- t2.rank + 1
       | _ -> assert false)

  let compare t1 t2 = Stdlib.compare t1.id t2.id     
end

module CongruenceClosure = struct
  let rec subterms t = 
    match Tm.out t with 
    | Z 
    | V _    -> Seq.return t 
    | S t' 
    | Fst t'
    | Snd t' -> Seq.cons t (subterms t')
    | App(t1, t2) 
    | Pair(t1, t2) -> Seq.cons t (Seq.concat [subterms t1; subterms t2])


  (* Create a union-find set for each subterm, doing something 
     sensible to avoid creating duplicate sets for repeated terms
     in  the stream*)

  let classes ts = 
    let i = Hashtbl.create 0 in 
    let insert t = 
      if Hashtbl.mem i t 
      then ()
      else Hashtbl.add i t (DisjointSet.create t)
    in
    Seq.iter insert ts;
    i 

  let find i (t : Tm.t) = 
    (DisjointSet.find (Hashtbl.find i t)).DisjointSet.value

  let equiv i e1 e2 = 
    Tm.(=) (find i e1) (find i e2)

  let congruent i e1 e2 = 
    if equiv i e1 e2 then 
      true
    else 
      (match Tm.out e1, Tm.out e2 with
       | V x, V y -> x = y
       | Z, Z -> true
       | Fst e1', Fst e2'
       | Snd e1', Snd e2'
       | S e1', S e2' -> equiv i e1' e2'
       | Pair(e1',e2'), Pair(e1'',e2'') 
       | App(e1',e2'), App(e1'',e2'') -> equiv i e1' e1'' && equiv i e2' e2''
       | _, _ -> false)

  let rec merge i (t1, t2) = 
    if equiv i t1 t2 then
      ()
    else
      let preds t = 
        (* Find all the terms equivalent to t *)
        let ts = DisjointSet.equiv (Hashtbl.find i t) in 
        (* Find each term's predecessors *)
        let tss = List.map Tm.predecessors ts in
        List.flatten tss 
      in 
      let pred1 = preds t1 in
      let pred2 = preds t2 in 
      List.iter (fun t1' -> 
          List.iter (fun t2' -> 
              if not (equiv i t1' t2') && congruent i t1' t2' then
                merge i (t1', t2')
              else
                ())
            pred2)
        pred1

  let closure es (t1, t2) = 
    let all_terms = 
      let tts = (t1, t2) :: es in
      let ts1, ts2 = List.split tts in 
      List.to_seq (List.concat [ts1; ts2])
    in
    let i = classes all_terms in
    List.iter (merge i) es;
    congruent i t1 t2 
end


type prop = 
  | True
  | And of prop * prop
  | Implies of prop * prop 
  | Bot
  | Or of prop * prop
  | Forall of var * prop
  | Exists of var * prop
  | Eq of Tm.t * Tm.t * sort

type pat = 
  | Var of string
  | Pair of pat * pat 
  | Left of pat
  | Right of pat

type pf = 
  | Unit
  | Tuple of pf * pf
  | Left of pf
  | Right of pf
  | Lam of var * pf
  | TLam of var * sort * pf
  | App of pf * arg list 
  | Pack of Tm.t * pf
  | Unpack of var * var * pf * pf 
  | Cases of pf * (pat * pf) list 
and arg = L of pf | A of Tm.t





