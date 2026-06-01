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
simp [solution_postcond] at h
have h_prec : 1 ≤ [1].length ∧ [1].length ≤ 100 ∧ [1].all (fun x => 1 ≤ x ∧ x ≤ 100) := by
  simp [List.all]
  norm_num
specialize h h_prec
obtain ⟨h_ge, h_eq⟩ := h
-- Compute what the implementation returns
simp [solution, List.length, List.foldl] at h_eq
-- Implementation: 1*(1+1)/2 - 1 = 1 - 1 = 0
have h_impl : 1 * (1 + 1) / 2 - 1 = 0 := by norm_num
rw [h_impl] at h_eq
-- Compute what the spec expects
-- For [1]: only one subarray [1] from index 0 to 0
-- getSubarray_local 0 0 = [1]
-- distinctCount_local [1] = 1
-- square_local 1 = 1
-- So expectedSum = 1
simp [List.range] at h_eq
-- List.range 1 = [0]
-- For outer loop: i = 0
-- List.range (1 - 0) = List.range 1 = [0]
-- For inner loop: d = 0, so j = 0 + 0 = 0
-- The expectedSum should be 1² = 1
-- We need to show 0 = 1 is false
have h_expected : (List.range 1).foldl (fun outerSum i =>
    outerSum + (List.range (1 - i)).foldl (fun currentInnerSum d =>
      let j := i + d
      let subarr := ([1].drop i).take (j - i + 1)
      let count := (subarr.foldl (fun seen x => if seen.elem x then seen else x :: seen) []).length
      currentInnerSum + count * count
    ) 0
  ) 0 = 1 := by
  simp [List.range, List.foldl, List.drop, List.take, List.elem]
  norm_num
rw [h_expected] at h_eq
norm_num at h_eq
