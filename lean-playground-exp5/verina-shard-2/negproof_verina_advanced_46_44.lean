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
  use [2, -5, 3], trivial
simp only [maxSubarraySum_postcond]
intro h_postcond
-- The implementation will return 3 (from Kadane starting with 2)
have h_impl : maxSubarraySum [2, -5, 3] trivial = 3 := by
  unfold maxSubarraySum
  -- Not all negative (2 and 3 are positive)
  simp
  -- Kadane will process: start with 2, then max(-5, 2+(-5))=max(-5,-3)=-3,
  -- then max(3, -3+3)=max(3,0)=3
  rfl
-- Apply postcondition with result = 3
rw [← h_impl] at h_postcond
obtain ⟨h_contains, h_all⟩ := h_postcond
-- The subarray [2] has sum 2, [3] has sum 3, [2,-5,3] has sum 0
-- But also [2,-5] has sum -3, [-5] has sum -5, [-5,3] has sum -2
-- And importantly: the empty subarray has sum 0
have h_zero_in : 0 ∈ (List.range ([2,-5,3].length + 1)).flatMap (fun start =>
    List.range ([2,-5,3].length - start + 1).map (fun len =>
      [2,-5,3].drop start |>.take len |>.sum)) := by
  simp only [List.length_cons, List.length_singleton, List.length_nil]
  use 0, 0
  simp [List.drop_zero, List.take_zero, List.sum_nil]
-- Check that [2] gives sum 2
have h_two_in : 2 ∈ (List.range ([2,-5,3].length + 1)).flatMap (fun start =>
    List.range ([2,-5,3].length - start + 1).map (fun len =>
      [2,-5,3].drop start |>.take len |>.sum)) := by
  simp only [List.length_cons, List.length_singleton, List.length_nil]
  use 0, 1
  simp [List.drop_zero, List.take_one, List.sum_singleton]
-- Actually, let me check [2, -5, 3] more carefully
-- The bug is that the implementation doesn't return the true maximum
-- Let me verify what all subarrays sum to
-- Actually, 3 is the correct maximum. Let me try a different example.
clear h_postcond h_impl h_contains h_all h_zero_in h_two_in
-- Try [-1] which should have max 0 (empty array) but returns -1
use [-1], trivial
simp only [maxSubarraySum_postcond]
intro h_postcond
have h_impl : maxSubarraySum [-1] trivial = -1 := by
  unfold maxSubarraySum
  simp
  rfl
rw [← h_impl] at h_postcond
obtain ⟨h_contains, h_all⟩ := h_postcond
-- Empty subarray has sum 0
have h_zero_in : 0 ∈ (List.range ([-1].length + 1)).flatMap (fun start =>
    List.range ([-1].length - start + 1).map (fun len =>
      [-1].drop start |>.take len |>.sum)) := by
  simp [List.length_singleton]
  use 0, 0
  simp [List.drop_zero, List.take_zero, List.sum_nil]
-- h_all says 0 ≤ -1, contradiction
have h_contradiction := h_all 0 h_zero_in
linarith
