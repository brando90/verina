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
-- h says: (16 % 8 = 0 ∨ ∃ i, 16 / 10^i % 10 = 8) ↔ isItEight 16 trivial = true
-- We'll show this is false by showing LHS is true but RHS is false
have lhs_true : 16 % 8 = 0 ∨ ∃ i, 16 / 10^i % 10 = 8 := by
  left
  norm_num
have rhs_false : isItEight 16 trivial = false := by
  rfl
rw [rhs_false] at h
simp at h
exact h lhs_true
