-- Stolen from: github.com/athas/raytracingthenextweekinfuthark and modified
-- s.t. we can construct octrees from the radix tree, by storing the delta
-- value of each inner node.

-- Based on "Maximizing Parallelism in the Construction of BVHs,
-- Octrees, and k-d Trees" by Tero Karras.

def div_rounding_up x y : i32 = (x + y - 1) / y

type ptr = #leaf i32 | #inner i32

type inner = {delta_node: i32, sfc_code: u32, left:ptr, right:ptr, parent: i32}

-- | `L` must be sorted.
def mk_radix_tree [n] (L: [n]u32) : []inner =

  let delta (i, j) =
    if j >= 0 && j < i32.i64 n
    then let Li = L[i]
         let Lj = L[j]
         -- Handle duplicates by using index as
         -- tiebreaker if necessary.
         in if Li == Lj
            then 32 + u32.clz (u32.i32 i ^ u32.i32 j)
            else u32.clz (Li ^ Lj)
    else -1

  let node i =
    let i = i32.i64 i
    -- Determine direction of range.
    let d = i32.sgn (delta(i,i+1) - delta(i,i-1))

    -- Compute upper bound for the length of the range.
    let delta_min = delta(i,i-d)
    let l_max = loop l_max = 2
                while delta(i, i+l_max*d) > delta_min do
                  l_max * 2

    -- Find the other end using binary search.
    let (l, _) = loop (l, t) = (0, l_max/2)
                 while t > 0 do
                   if delta(i, i+(l+t)*d) > delta_min
                   then (l + t, t/2)
                   else (l, t/2)
    let j = i + l * d

    -- Find the split position using binary search.
    let delta_node = delta(i, j)
    let (s, _) = loop (s, q) = (0, 1)
                 while q <= l do
                 let t = l `div_rounding_up` (q*2)
                 in if delta(i, i+(s+t)*d) > delta_node
                    then (s+t, q*2)
                    else (s, q*2)
    let gamma = i + s*d + i32.min d 0

    -- Output child pointers
    let (left, set_left_parent) =
      if i32.min i j == gamma
      then (#leaf gamma, -1)
      else (#inner gamma, gamma)

    let (right, set_right_parent) =
      if i32.max i j == gamma + 1
      then (#leaf (gamma+1), -1)
      else (#inner (gamma+1), gamma+1)
    let sfc_code = L[i] >> (32 - (u32.i32 delta_node))
    in ({delta_node, sfc_code, left, right}, (set_left_parent, i), (set_right_parent, i))

  let (inners, parents_a, parents_b) = tabulate (n-1) node |> unzip3
  let k = (n-1)*2
  let parents = scatter (replicate (n-1) (-1))
                        (concat_to k
                                   (map ((.0) >-> i64.i32) parents_a)
                                   (map ((.0) >-> i64.i32) parents_b))
                        (concat_to k
                                   (map (.1) parents_a)
                                   (map (.1) parents_b))

  in map2 (\{delta_node, sfc_code, left, right} parent ->
    {delta_node, sfc_code, left, right, parent}) inners parents
