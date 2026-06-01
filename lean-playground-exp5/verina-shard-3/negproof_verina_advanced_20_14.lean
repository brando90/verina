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
unfold isItEight_postcond
intro h
-- The left side of the biconditional is true because 16 % 8 = 0
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By h.mp, since the left side is true, isItEight 16 must be true
have right_true : isItEight 16 trivial = true := h.mp left_true
-- But we can compute that isItEight 16 = false
unfold isItEight at right_true
simp [Int.natAbs] at right_true
-- Now we need to show hasDigitEight 16 = false by unfolding the recursion
have eval_false : isItEight.hasDigitEight 16 = false := by
  unfold isItEight.hasDigitEight
  simp
  constructor
  · norm_num
  · unfold isItEight.hasDigitEight
    simp
    norm_num
rw [eval_false] at right_true
-- This gives us false = true, which is impossible
exact Bool.false_ne_true right_true
