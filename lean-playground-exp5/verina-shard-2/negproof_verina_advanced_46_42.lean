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
-- The implementation returns -1 for input [-1]
have h_impl : maxSubarraySum [-1] trivial = -1 := by
  unfold maxSubarraySum
  simp
  rfl
rw [h_impl]
-- Show the postcondition is false
intro h
obtain ⟨h_contains, h_all⟩ := h
-- The empty subarray has sum 0
have h_zero : 0 ∈ (List.range ([-1].length + 1)).flatMap (fun start =>
    List.range ([-1].length - start + 1).map (fun len =>
      [-1].drop start |>.take len |>.sum)) := by
  simp [List.length_singleton, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_nil, List.mem_cons, List.mem_singleton]
  left
  simp [List.range_one, List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton]
  left
  simp [List.drop_zero, List.take_zero, List.sum_nil]
-- Apply h_all to get 0 ≤ -1
have h_contradiction := h_all 0 h_zero
-- This is a contradiction
linarith
