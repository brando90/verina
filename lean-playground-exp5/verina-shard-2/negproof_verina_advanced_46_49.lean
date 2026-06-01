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
  use [-2, 1, -3], trivial
simp only [maxSubarraySum_postcond]
intro h_postcond
-- The implementation returns -1 for input [-2, 1, -3]
have h_impl : maxSubarraySum [-2, 1, -3] trivial = -1 := by
  unfold maxSubarraySum
  simp [isAllNegative]
  norm_num
  rfl
-- Apply the postcondition
have ⟨h_contains, h_all⟩ := h_postcond h_impl
-- Show that 1 is in subArraySums (subarray [1])
have h_one_in : 1 ∈ (List.range ([-2, 1, -3].length + 1)).flatMap (fun start =>
    List.range ([-2, 1, -3].length - start + 1).map (fun len =>
      [-2, 1, -3].drop start |>.take len |>.sum)) := by
  simp [List.length]
  use 1, 1
  simp [List.drop, List.take, List.sum]
-- Apply h_all to 1
have h_contradiction := h_all 1 h_one_in
-- We have 1 ≤ -1 which is false
norm_num at h_contradiction
