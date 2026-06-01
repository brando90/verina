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
  use [-1]
use True.intro
simp [maxSubarraySum_postcond]
-- Compute maxSubarraySum [-1]
have h_result : maxSubarraySum [-1] True.intro = -1 := by
  simp [maxSubarraySum]
  rfl
rw [h_result]
-- Show that the postcondition doesn't hold
simp [List.range, List.flatMap, List.map, List.drop, List.take, List.sum]
-- The subarray sums are: [-1] (the full array) and 0 (empty subarray)
-- So we need to show that ¬([0, -1].contains (-1) ∧ [0, -1].all (· ≤ -1))
simp [List.contains, List.all]
-- This simplifies to showing that ¬(0 ≤ -1), which is true
norm_num
