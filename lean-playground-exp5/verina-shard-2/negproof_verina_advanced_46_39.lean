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
-- The implementation returns -1
have h_result : maxSubarraySum [-1] trivial = -1 := rfl
rw [h_result]
-- Show that the postcondition is false
push_neg
-- We need to show either:
-- 1. -1 is not in subArraySums, or
-- 2. There exists an element in subArraySums that is > -1
right
-- Choose the second option: show 0 > -1
use 0
constructor
· -- Show 0 is in subArraySums (it's the sum of the empty subarray)
  simp only [List.length_singleton]
  simp only [List.mem_flatMap]
  use 0
  constructor
  · simp only [List.mem_range]
    norm_num
  · simp only [List.mem_map]
    use 0
    constructor
    · simp only [List.mem_range]
      norm_num
    · simp only [List.drop_zero, List.take_zero, List.sum_nil]
· -- Show 0 > -1
  norm_num
