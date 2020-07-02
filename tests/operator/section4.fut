-- Operator section with interesting type to the left.
-- ==
-- input { [-1,1] } output { [1,3] }

let (<*>) 'a 'b (f: a -> b) (xs: a) =
  f xs

let main (xs: []i32) =
  (<*>map (2+) xs) id
