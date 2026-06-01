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
have h_result : maxSubarraySum [-1] trivial = -1 := by
  simp only [maxSubarraySum]
  simp only [maxSubarraySum.isAllNegative]
  decide
rw [h_result] at h
cases' h with h_contains h_all
-- The empty subarray has sum 0
have h_empty_sum : 0 ∈ (List.range ([-1].length + 1)).flatMap (fun start =>
    (List.range ([-1].length - start + 1)).map (fun len =>
      ([-1].drop start).take len).sum) := by
  simp only [List.length, List.range, List.flatMap, List.map]
  simp only [List.drop, List.take, List.sum, List.mem_cons, List.mem_singleton]
  left
  rfl
have h_not_all : ¬((List.range ([-1].length + 1)).flatMap (fun start =>
    (List.range ([-1].length - start + 1)).map (fun len =>
      ([-1].drop start).take len).sum)).all (· ≤ -1) := by
  simp only [List.all, List.length, List.range, List.flatMap, List.map]
  simp only [List.drop, List.take, List.sum]
  simp only [decide, List.forall_mem_cons, List.forall_mem_singleton]
  norm_num
exact h_not_all h_all
