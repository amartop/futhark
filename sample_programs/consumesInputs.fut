

let f (ys : *[]i64) : *[]i64 = ys with [0] = 5

entry main (k : i64) : [][]i64 =
  let z = map (\x -> iota 10) (replicate 10 0)
  let a = map (map (+1)) z
  let b = map f a
  in b
