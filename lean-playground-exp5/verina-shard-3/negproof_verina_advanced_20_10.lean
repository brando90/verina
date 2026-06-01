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
-- The biconditional states: (16 % 8 = 0 ∨ ∃ i, 16 / 10^i % 10 = 8) ↔ isItEight 16 trivial
-- Left side is true because 16 % 8 = 0
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By the biconditional, isItEight 16 trivial must be true
have right_true : isItEight 16 trivial = true := h.mp left_true
-- But by computation, isItEight 16 trivial = false
have right_false : isItEight 16 trivial = false := by
  rfl
-- Contradiction
rw [right_false] at right_true
exact Bool.false_ne_true right_true
