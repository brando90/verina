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
-- Show that 16 % 8 = 0, so the left side of the biconditional is true
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By the biconditional in h, isItEight 16 must be true
have : isItEight 16 trivial = true := h.mp left_true
-- But isItEight 16 actually returns false
simp only [isItEight] at this
-- Unfold hasDigitEight to show it returns false for 16
have : (let rec hasDigitEight : Nat → Bool
  | 0 => false
  | m => if m % 10 = 8 then true else hasDigitEight (m / 10)
  hasDigitEight (Int.natAbs 16)) = true := this
simp only [Int.natAbs] at this
-- Evaluate hasDigitEight 16
have eval : (let rec hasDigitEight : Nat → Bool
  | 0 => false
  | m => if m % 10 = 8 then true else hasDigitEight (m / 10)
  hasDigitEight 16) = false := by
  native_decide
rw [eval] at this
exact Bool.false_ne_true this
