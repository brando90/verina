@[reducible, simp]
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  if k == 0 then 0
  else
    let rec count (l : List Nat) (acc : Nat) : Nat :=
      match l with
      | [] => acc
      | x :: xs => if x < k then count xs (acc + 1) else count xs acc
    count nums 0
@[reducible, simp]
def minOperations_postcond (nums : List Nat) (k : Nat) (result : Nat) (h_precond : minOperations_precond (nums) (k)) :=
  -- define the list of elements processed after `result` operations
  let processed := (nums.reverse).take result
  -- define the target numbers to collect (1 to k)
  let target_nums := (List.range k).map (· + 1)

  -- condition 1: All target numbers must be present in the processed elements
  let collected_all := target_nums.all (fun n => List.elem n processed)

  -- condition 2: `result` must be the minimum number of operations.
  -- This means either result is 0 (which implies k must be 0 as target_nums would be empty)
  -- or result > 0, and taking one less operation (result - 1) is not sufficient
  let is_minimal :=
    if result > 0 then
      -- if one fewer element is taken, not all target numbers should be present
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      -- if result is 0, it can only be minimal if k is 0 (no targets required)
      -- So if k=0, `collected_all` is true. If result=0, this condition `k==0` ensures minimality.
      k == 0

  -- overall specification:
  collected_all ∧ is_minimal

theorem minOperations_spec_violated : ∃ nums k,
    ∃ (h_precond : minOperations_precond (nums) (k)),
    ¬ minOperations_postcond (nums) (k) (minOperations (nums) (k) h_precond) h_precond := by
  use [2, 1], 2
have h_pre : minOperations_precond [2, 1] 2 := by
  simp only [minOperations_precond]
  simp only [List.range, List.map, List.all, List.elem]
  constructor
  · simp
  · simp
use h_pre
simp only [minOperations_postcond, minOperations]
simp only [decide_eq_true_eq, ite_false]
-- The implementation counts elements < 2, which is just 1
have count_eq : minOperations.count [2, 1] 0 = 1 := by
  simp only [minOperations.count]
  norm_num
  simp only [minOperations.count]
  norm_num
simp only [count_eq]
-- Now check postcondition with result = 1
simp only [List.range, List.map]
-- reverse [2, 1] = [1, 2], take 1 [1, 2] = [1]
have rev_eq : List.reverse [2, 1] = [1, 2] := by rfl
simp only [rev_eq]
have take_eq : List.take 1 [1, 2] = [1] := by rfl
simp only [take_eq]
simp only [List.all, List.elem]
-- We need to show ¬(1 ∈ [1] ∧ 2 ∈ [1] ∧ is_minimal)
-- 2 ∉ [1], so collected_all is false
simp only [decide_eq_true_eq, decide_eq_false_iff_not]
norm_num
