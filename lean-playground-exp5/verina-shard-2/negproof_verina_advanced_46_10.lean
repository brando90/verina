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

-- Step 1: Show that maxSubarraySum [-1] True.intro = -1
have h_result : maxSubarraySum [-1] True.intro = -1 := by
  rfl

-- Step 2: Apply the result to the postcondition
unfold maxSubarraySum_postcond at h_post
rw [h_result] at h_post
obtain ⟨_, h_all⟩ := h_post

-- Step 3: Show that 0 is a subarray sum (the empty subarray)
have h_zero_sum : 0 ∈ List.range ([-1].length + 1) |>.flatMap (fun start =>
    List.range ([-1].length - start + 1) |>.map (fun len =>
      [-1].drop start |>.take len |>.sum)) := by
  simp [List.length, List.range, List.flatMap, List.map]
  use 0, 0
  simp [List.drop, List.take, List.sum]

-- Step 4: Apply h_all to get 0 ≤ -1, which is false
have h_contra := h_all 0 h_zero_sum
linarith
