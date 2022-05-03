

entry main (xs : [5][4]i32) : [4][5]i32 =
  let (ys, zs) = unzip ( (map (\x -> (map (+1) x, map (+2) x))) xs)
  let zs = map2 (map2 (+)) (transpose ys) (transpose zs)
  in zs
