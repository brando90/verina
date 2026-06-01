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
simp only [solution_precond]
use ⟨by simp, by simp, by simp [List.all]⟩
simp only [solution_postcond, solution]
intro h
have h_prec : 1 ≤ 1 ∧ 1 ≤ 100 ∧ [1].all (fun x => 1 ≤ x ∧ x ≤ 100) := by
  simp [List.all]
specialize h h_prec
obtain ⟨h_ge, h_eq⟩ := h
simp [List.length, List.foldl] at h_eq
-- The implementation returns: 1*(1+1)/2 - 1 = 1 - 1 = 0
-- The spec expects: for [1], there's one subarray [1] with 1 distinct element
-- So expected = 1² = 1
-- We need to show 0 = expectedSum is false
have h_impl : 1 * (1 + 1) / 2 - 1 = 0 := by norm_num
rw [h_impl] at h_eq
clear h_impl h_ge h_prec h
-- Now we need to compute the expectedSum
simp [List.range, List.foldl] at h_eq
-- For i = 0, j = 0: subarray is [1], distinct count = 1, square = 1
-- So expectedSum = 1
norm_num at h_eq
