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
-- The specification states: (16 % 8 = 0 ∨ ∃ i, |16| / 10^i % 10 = 8) ↔ isItEight 16 trivial
-- First, we show the left side is true because 16 % 8 = 0
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By the biconditional, this means isItEight 16 trivial must be true
have : isItEight 16 trivial = true := h.mp left_true
-- But we can compute that isItEight 16 trivial = false
simp only [isItEight, Int.natAbs] at this
-- Now we need to show hasDigitEight 16 = false
have : isItEight.hasDigitEight 16 = false := by
  rw [isItEight.hasDigitEight]
  simp
  constructor
  · norm_num
  · rw [isItEight.hasDigitEight]
    simp
    norm_num
-- This gives us true = false, which is a contradiction
simp at this
