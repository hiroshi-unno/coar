let rec sum_acc i n sum =
  if i < n then sum_acc (i + 1) n (sum + i) else sum
let rec sum_acc_minus i n sum =
  if i < n then sum_acc_minus (i + 1) n (sum - i) else sum
let main n sum_middle sum0 i0 =
  let sum1 = sum_acc i0 n sum0 in
  let sum2 = sum_acc_minus i0 n sum_middle in
  (* if sum1 = sum_middle then *) assert(sum1 + sum2 = sum0 + sum_middle)
