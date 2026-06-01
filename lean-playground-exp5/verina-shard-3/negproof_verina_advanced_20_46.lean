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
-- 16 is divisible by 8, so left side of iff is true
have h1 : (16 : Int) % 8 = 0 := by norm_num
have h2 : (16 : Int) % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := Or.inl h1
-- By the biconditional, isItEight 16 should be true
have h3 : isItEight 16 trivial = true := h.mp h2
-- But isItEight 16 returns false
have h4 : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs_of_nonneg (by norm_num : (16 : Int) ≥ 0)]
  -- hasDigitEight 16 should be false
  have : isItEight.hasDigitEight 16 = false := by
    rw [isItEight.hasDigitEight]
    simp only [decide_eq_false_iff_not, not_or]
    constructor
    · norm_num
    · simp only [ite_eq_left_iff, Bool.not_eq_true, ite_eq_right_iff]
      intro _
      norm_num
      rw [isItEight.hasDigitEight]
      simp only [decide_eq_false_iff_not, not_or]
      constructor
      · norm_num
      · simp only [ite_eq_left_iff, Bool.not_eq_true]
        intro _
        norm_num
  exact this
rw [h4] at h3
exact Bool.false_ne_true h3
