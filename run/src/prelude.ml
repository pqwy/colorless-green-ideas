
let rec fmap f = function
  []    -> []
| x::xs -> match f x with None -> fmap f xs | Some a -> a :: fmap f xs

let id x = x
