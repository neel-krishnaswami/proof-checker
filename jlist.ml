type 'a t' = 
  | Zero 
  | One of 'a 
  | Append of 'a t * 'a t 
and 'a t = 'a t' * int 


let size : 'a t -> int = snd 
let data : 'a t -> 'a t' = fst

let zero = (Zero, 0)
let one x = (One x, 1)

let rec split xs = 
  match data xs with
  | Zero -> zero, zero
  | One x -> (one x), zero 
  | Append(ys, zs) -> (ys, zs)
          

let rec append xs ys = 
  let nx = size xs in
  let ny = size ys in 
  if ny >= 2 * nx + 1 then
    let (ys1, ys2) = split ys in
    (Append(append xs ys1, ys2), nx + ny)
  else if nx >= 2 * ny + 1 then
    let (xs1, xs2) = split xs in 
    (Append(xs1, append xs2 ys), nx + ny)
  else
    (Append(xs, ys), nx + ny)


