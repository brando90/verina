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
intro h_post
simp [maxSubarraySum_postcond] at h_post
-- Compute the result
have h_comp : maxSubarraySum [-1] True.intro = -1 := by
  unfold maxSubarraySum
  simp
  rfl
rw [h_comp] at h_post
-- Extract the second part of the postcondition
obtain ⟨_, h_all⟩ := h_post
-- Check that 0 is in the subarray sums (empty subarray)
have h_zero : 0 ∈ (List.range 2).flatMap (fun start =>
    (List.range (1 - start + 1)).map (fun len =>
      ([-1].drop start).take len).sum)) := by
  simp [List.range, List.flatMap, List.map, List.drop, List.take, List.sum]
  left
  rfl
-- Apply h_all to 0
have h_contra := h_all 0 h_zero
-- But 0 ≤ -1 is false
norm_num at h_contra
