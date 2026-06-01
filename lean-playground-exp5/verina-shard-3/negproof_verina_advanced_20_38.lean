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
-- Show that 16 % 8 = 0
have h1 : (16 : Int) % 8 = 0 := by norm_num
-- So the left side of the biconditional is true
have h2 : (16 : Int) % 8 = 0 ∨ ∃ i, Int.natAbs 16 / 10 ^ i % 10 = 8 := Or.inl h1
-- By the biconditional, isItEight 16 should be true
have h3 : isItEight 16 trivial = true := h.mp h2
-- But isItEight 16 is false
have h4 : isItEight 16 trivial = false := by
  unfold isItEight
  simp only [Int.natAbs]
  -- hasDigitEight 16 = if 16 = 0 then false else if 16 % 10 = 8 then true else hasDigitEight (16 / 10)
  -- 16 ≠ 0, 16 % 10 = 6 ≠ 8, so recurse with 16 / 10 = 1
  -- hasDigitEight 1 = if 1 = 0 then false else if 1 % 10 = 8 then true else hasDigitEight (1 / 10)
  -- 1 ≠ 0, 1 % 10 = 1 ≠ 8, so recurse with 1 / 10 = 0
  -- hasDigitEight 0 = if 0 = 0 then false else ...
  -- returns false
  rfl
-- Contradiction
rw [h4] at h3
exact Bool.false_ne_true h3
