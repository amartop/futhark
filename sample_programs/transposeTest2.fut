-- transposeTest2.fut


entry main (xs : [5][4]i32) : [4][5]i32 =
  let ys = map (map (+1)) xs
  let zs = map2 (map2 (+)) (transpose ys) (transpose ys)
  in zs
