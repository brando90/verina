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
-- We'll show that the biconditional leads to a contradiction
-- First, establish that 16 % 8 = 0
have h1 : 16 % 8 = 0 := by norm_num
-- So the left side of the biconditional is true
have h2 : 16 % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := Or.inl h1
-- By the biconditional, isItEight 16 trivial should be true
have h3 : isItEight 16 trivial = true := h.mp h2
-- But we can compute that isItEight 16 trivial = false
have h4 : isItEight 16 trivial = false := rfl
-- This is a contradiction
rw [h4] at h3
exact Bool.false_ne_true h3
