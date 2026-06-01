import Std.Data.HashSet
open Std

@[reducible, simp]
def solution_precond (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

def solution (nums : List Nat) (h_precond : solution_precond (nums)) : Nat :=
  let n := nums.length
  let sum_actual := nums.foldl (· + ·) 0
  let sum_expected := n * (n + 1) / 2
  sum_expected - sum_actual
@[reducible, simp]
def solution_postcond (nums : List Nat) (result : Nat) (h_precond : solution_precond (nums)) :=
  let n := nums.length;

  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);

  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;

  let square_local := fun (n : Nat) => n * n;

  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;

    result = expectedSum
  )

theorem solution_spec_violated : ∃ nums,
    ∃ (h_precond : solution_precond (nums)),
    ¬ solution_postcond (nums) (solution (nums) h_precond) h_precond := by
  use [1]
use ⟨by norm_num, by norm_num, by simp [List.all]; norm_num⟩
intro h
simp [solution_postcond, solution] at h
have precond : 1 ≤ [1].length ∧ [1].length ≤ 100 ∧ [1].all (fun x => 1 ≤ x ∧ x ≤ 100) := by
  simp [List.all]
  norm_num
specialize h precond
cases h with
| intro h_ge h_rest =>
  cases h_rest with
  | intro _ h_eq =>
    -- The implementation returns: 1*(1+1)/2 - 1 = 1 - 1 = 0
    -- Let's compute what the spec expects
    simp at h_eq
    -- For list [1] with length 1:
    -- There's only one subarray: from index 0 to 0 (the subarray [1])
    -- This subarray has 1 distinct element
    -- So the expected sum is 1² = 1
    -- But the implementation returns 0
    norm_num at h_eq
