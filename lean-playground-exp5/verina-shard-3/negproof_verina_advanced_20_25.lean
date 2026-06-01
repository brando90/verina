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
-- The left side of the biconditional is true because 16 % 8 = 0
have left_true : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By the biconditional h, since the left side is true, the right side must be true
have right_should_be_true : isItEight 16 trivial = true := h.mp left_true
-- But actually isItEight 16 returns false
have right_is_false : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs]
  -- hasDigitEight 16 returns false because 16 doesn't contain digit 8
  rfl
-- This gives us a contradiction
rw [right_is_false] at right_should_be_true
exact Bool.noConfusion right_should_be_true
