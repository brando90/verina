@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  True

def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  let rec isAllNegative (l : List Int) : Bool :=
    match l with | [] => true | x :: xs => x < 0 && isAllNegative xs
  if isAllNegative numbers then
    numbers.foldl max (numbers[0]!)
  else
    let rec kadane (l : List Int) (curMax globalMax : Int) : Int :=
      match l with
      | [] => globalMax
      | x :: rest =>
        let curMax := max x (curMax + x)
        kadane rest curMax (max globalMax curMax)
    match numbers with
    | [] => 0
    | x :: rest => kadane rest x x
@[reducible, simp]
def maxSubarraySum_postcond (numbers : List Int) (result : Int) (h_precond : maxSubarraySum_precond (numbers)) :=
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

theorem maxSubarraySum_spec_violated : ∃ numbers,
    ∃ (h_precond : maxSubarraySum_precond (numbers)),
    ¬ maxSubarraySum_postcond (numbers) (maxSubarraySum (numbers) h_precond) h_precond := by
  use [-1], trivial
simp only [maxSubarraySum_postcond]
push_neg
-- The implementation returns -1 for input [-1]
have h_impl : maxSubarraySum [-1] trivial = -1 := by
  rfl
exists h_impl
-- Now show there's a subarray sum that is not ≤ -1
use 0
constructor
· -- Show that 0 is in the list of subarray sums (empty subarray)
  simp only [List.mem_iff_exists_mem_flatMap]
  use 0
  constructor
  · simp only [List.length_singleton, List.mem_range]
    norm_num
  · simp only [List.mem_map]
    use 0
    constructor
    · simp only [List.length_singleton, List.mem_range]
      norm_num
    · simp only [List.drop_zero, List.take_zero, List.sum_nil]
· -- Show that 0 > -1
  norm_num
