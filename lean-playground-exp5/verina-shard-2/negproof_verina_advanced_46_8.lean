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

-- First, compute what maxSubarraySum returns
have h_result : maxSubarraySum [-1] True.intro = -1 := by
  unfold maxSubarraySum
  -- isAllNegative returns true for [-1]
  have h_all_neg : (let rec isAllNegative (l : List Int) : Bool :=
    match l with | [] => true | x :: xs => x < 0 && isAllNegative xs
    isAllNegative [-1]) = true := by simp
  simp [h_all_neg]
  -- So it returns foldl max on [-1] starting with [-1][0]! = -1
  simp [List.foldl]

-- Now show the postcondition is violated
unfold maxSubarraySum_postcond at h_post
simp only [h_result] at h_post
obtain ⟨_, h_all⟩ := h_post

-- The empty subarray has sum 0
have h_empty_sum : 0 ∈ (List.range 2).flatMap (fun start =>
    (List.range (1 - start + 1)).map (fun len =>
      ([-1].drop start).take len).sum)) := by
  simp [List.range, List.flatMap, List.map]
  use 0
  simp
  use 0
  simp [List.drop, List.take, List.sum]

-- From h_all, we get 0 ≤ -1
have h_contra := h_all 0 h_empty_sum
-- This is a contradiction
norm_num at h_contra
