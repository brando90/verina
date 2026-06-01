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
-- First compute what maxSubarraySum returns
have h_result : maxSubarraySum [-1] True.intro = -1 := by
  unfold maxSubarraySum
  -- Check that isAllNegative returns true
  have h_neg : (let rec isAllNegative (l : List Int) : Bool :=
    match l with | [] => true | x :: xs => x < 0 && isAllNegative xs
    isAllNegative [-1]) = true := by
    simp
    decide
  -- So it returns the max of the list
  simp [h_neg]
  decide

-- Now let's examine the postcondition
unfold maxSubarraySum_postcond at h_post
simp only [h_result] at h_post
obtain ⟨h_contains, h_all⟩ := h_post

-- The subarray sums include 0 (from the empty subarray)
have h_zero_in : 0 ∈ List.range ([-1].length + 1) |>.flatMap (fun start =>
    List.range ([-1].length - start + 1) |>.map (fun len =>
      [-1].drop start |>.take len |>.sum)) := by
  simp [List.range, List.flatMap, List.map, List.length]
  use 0, 0
  simp [List.drop, List.take, List.sum]

-- Apply h_all to show that 0 ≤ -1
have h_contra := h_all 0 h_zero_in
-- But this is false
linarith
