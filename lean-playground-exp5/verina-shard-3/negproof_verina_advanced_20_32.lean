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
have left_true : (16 : Int) % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- By h, since left side is true, right side must be true
have should_be_true : isItEight 16 trivial = true := h.mp left_true
-- But isItEight 16 is false (checking manually)
have is_false : isItEight 16 trivial = false := by
  simp only [isItEight]
  -- hasDigitEight 16
  simp only [isItEight.hasDigitEight]
  -- 16 ≠ 0, so check 16 % 10 = 8
  simp only [decide, Nat.mod_eq_of_lt, Nat.div_eq_of_lt]
  -- 16 % 10 = 6 ≠ 8, so recurse on 16 / 10 = 1
  -- hasDigitEight 1
  -- 1 ≠ 0, so check 1 % 10 = 8
  -- 1 % 10 = 1 ≠ 8, so recurse on 1 / 10 = 0
  -- hasDigitEight 0 = false
  rfl
-- Contradiction
rw [is_false] at should_be_true
contradiction
