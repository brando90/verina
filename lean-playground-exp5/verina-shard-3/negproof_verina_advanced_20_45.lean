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
-- 16 is divisible by 8
have h1 : (16 : Int) % 8 = 0 := by norm_num
-- So the left side of the iff is true
have h2 : (16 : Int) % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := Or.inl h1
-- By the biconditional, isItEight 16 should be true
have h3 : isItEight 16 trivial = true := h.mp h2
-- But isItEight 16 actually returns false
have h4 : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs_of_nonneg (by norm_num : (16 : Int) ≥ 0)]
  -- Now we need to show hasDigitEight 16 = false
  rw [hasDigitEight]
  simp only [decide_False]
  -- 16 % 10 = 6 ≠ 8
  norm_num
  -- Now hasDigitEight (16 / 10) = hasDigitEight 1
  rw [hasDigitEight]
  simp only [decide_False]
  -- 1 % 10 = 1 ≠ 8
  norm_num
  -- Now hasDigitEight (1 / 10) = hasDigitEight 0
  rw [hasDigitEight]
  -- 0 = 0 is true
  simp only [decide_True, ite_true]
-- Contradiction
rw [h4] at h3
exact Bool.false_ne_true h3
