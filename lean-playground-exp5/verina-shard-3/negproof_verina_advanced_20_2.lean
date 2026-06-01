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
simp [isItEight_postcond, isItEight]
-- Need to show: ¬((16 % 8 = 0 ∨ ∃ i, 16 / 10 ^ i % 10 = 8) ↔ isItEight.hasDigitEight 16 = true)
-- First compute isItEight.hasDigitEight 16
have h_false : isItEight.hasDigitEight 16 = false := by
  rw [isItEight.hasDigitEight]
  simp
  -- 16 ≠ 0, so continue
  -- 16 % 10 = 6 ≠ 8, so check hasDigitEight (16 / 10)
  norm_num
  -- Now compute hasDigitEight 1
  rw [isItEight.hasDigitEight]
  simp
  -- 1 ≠ 0, so continue
  -- 1 % 10 = 1 ≠ 8, so check hasDigitEight (1 / 10)
  norm_num
  -- hasDigitEight 0 = false by definition
  rfl
rw [h_false]
simp
-- Now we need to show: (16 % 8 = 0 ∨ ∃ i, 16 / 10 ^ i % 10 = 8)
-- We'll show the left side: 16 % 8 = 0
left
norm_num
