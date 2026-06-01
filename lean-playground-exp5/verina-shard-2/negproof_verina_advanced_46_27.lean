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
intro h
simp only [maxSubarraySum_postcond] at h
-- Compute what the implementation returns for [-1]
have h_result : maxSubarraySum [-1] trivial = -1 := by
  unfold maxSubarraySum
  -- Check that isAllNegative [-1] = true
  have : maxSubarraySum.isAllNegative [-1] = true := by
    unfold maxSubarraySum.isAllNegative
    simp
  rw [this]
  simp
  -- numbers.foldl max (numbers[0]!) = -1
  rfl
-- Apply the result
rw [h_result] at h
obtain ⟨h_contains, h_all⟩ := h
-- The empty subarray has sum 0 and must be in subArraySums
have h_zero_in : 0 ∈ (List.range ([-1].length + 1)).flatMap (fun start =>
    (List.range ([-1].length - start + 1)).map (fun len =>
      ([-1].drop start).take len).sum) := by
  simp only [List.length, List.cons, List.nil, List.range]
  simp only [List.flatMap, List.map, List.drop, List.take, List.sum]
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  -- When start = 0 and len = 0, we get the empty list with sum 0
  left
  simp only [List.take, List.sum, List.foldr]
-- But h_all says all elements (including 0) are ≤ -1
have h_bad : 0 ≤ -1 := h_all 0 h_zero_in
-- This is a contradiction
linarith
