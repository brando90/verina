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
simp only [isItEight_postcond, isItEight]
-- We need to show the implementation and specification disagree
-- First, let's compute what the implementation returns
have impl_result : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs]
  -- Now we need to show hasDigitEight 16 = false
  have h1 : isItEight.hasDigitEight 16 = false := by
    unfold isItEight.hasDigitEight
    simp
    -- 16 % 10 = 6 ≠ 8
    norm_num
    -- Now check hasDigitEight (16 / 10) = hasDigitEight 1
    unfold isItEight.hasDigitEight
    simp
    -- 1 % 10 = 1 ≠ 8
    norm_num
    -- hasDigitEight (1 / 10) = hasDigitEight 0 = false
    rfl
  exact h1
-- Now show the specification says it should be true
have spec_true : 16 % 8 = 0 ∨ ∃ i, 16 / 10 ^ i % 10 = 8 := by
  left
  norm_num
-- The implementation returns false but specification says it should be true
rw [impl_result]
simp
exact spec_true
