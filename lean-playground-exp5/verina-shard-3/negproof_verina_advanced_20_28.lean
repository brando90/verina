@[reducible, simp]
def isItEight_precond (n : Int) : Prop :=
  True

def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  let rec hasDigitEight (m : Nat) : Bool :=
    if m = 0 then false
    else if m % 10 = 8 then true
    else hasDigitEight (m / 10)
  hasDigitEight n.natAbs
@[reducible, simp]
def isItEight_postcond (n : Int) (result : Bool) (h_precond : isItEight_precond (n)) :=
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result

theorem isItEight_spec_violated : ∃ n,
    ∃ (h_precond : isItEight_precond (n)),
    ¬ isItEight_postcond (n) (isItEight (n) h_precond) h_precond := by
  use 16
use trivial
simp only [isItEight_postcond]
intro h
-- The left side is true because 16 % 8 = 0
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  simp
-- By the biconditional, isItEight 16 should be true
have should_be_true : isItEight 16 trivial = true := by
  exact h.mp left_true
-- But isItEight 16 is actually false
have is_false : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs]
  -- Need to unfold hasDigitEight and compute
  unfold isItEight.hasDigitEight
  simp
  -- 16 % 10 = 6 ≠ 8, so we recurse with 16 / 10 = 1
  -- 1 % 10 = 1 ≠ 8, so we recurse with 1 / 10 = 0
  -- 0 = 0 returns false
  rfl
-- This is a contradiction
rw [is_false] at should_be_true
simp at should_be_true
