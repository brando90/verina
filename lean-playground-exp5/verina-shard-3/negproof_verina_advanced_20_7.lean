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
push_neg
constructor
· -- Show the biconditional doesn't hold
  intro h
  -- h : (16 % 8 = 0 ∨ ∃ i, 16 / 10 ^ i % 10 = 8) ↔ isItEight 16 trivial = true
  -- We know LHS is true because 16 % 8 = 0
  have lhs_true : 16 % 8 = 0 ∨ ∃ i, 16 / 10 ^ i % 10 = 8 := by
    left
    norm_num
  -- And we can compute that RHS is false
  have rhs_false : isItEight 16 trivial = false := by
    rfl
  -- From the biconditional and lhs_true, we get isItEight 16 trivial = true
  have : isItEight 16 trivial = true := h.mp lhs_true
  -- But this contradicts rhs_false
  rw [rhs_false] at this
  exact Bool.false_ne_true this
