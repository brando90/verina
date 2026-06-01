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
constructor
simp [isItEight_postcond, isItEight]
-- The implementation returns false because 16 doesn't contain digit 8
-- But the specification should return true because 16 % 8 = 0
simp [isItEight.hasDigitEight]
-- Show that hasDigitEight 16 = false
have h1 : isItEight.hasDigitEight 16 = false := by
  unfold isItEight.hasDigitEight
  simp
  -- 16 % 10 = 6 ≠ 8
  norm_num
  -- hasDigitEight (16 / 10) = hasDigitEight 1
  unfold isItEight.hasDigitEight
  simp
  -- 1 % 10 = 1 ≠ 8
  norm_num
  -- hasDigitEight (1 / 10) = hasDigitEight 0
  unfold isItEight.hasDigitEight
  simp
rw [h1]
simp
-- Now show that 16 % 8 = 0
norm_num
