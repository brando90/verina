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
simp [isItEight_precond]
constructor
simp [isItEight_postcond, isItEight]
intro h
cases h with
| inl h_div8 =>
  -- 16 % 8 = 0, so this case holds
  simp at h_div8
| inr h_digit8 =>
  -- Need to show: ¬∃ i, 16 / (10^i) % 10 = 8
  obtain ⟨i, hi⟩ := h_digit8
  simp at hi
  -- Check all possible values of i
  cases i with
  | zero =>
    -- 16 / 1 % 10 = 16 % 10 = 6 ≠ 8
    simp at hi
  | succ i =>
    cases i with
    | zero =>
      -- 16 / 10 % 10 = 1 % 10 = 1 ≠ 8
      simp at hi
    | succ i =>
      -- 16 / (10^(i+2)) = 0 for i ≥ 0, so 0 % 10 = 0 ≠ 8
      have : 16 / (10^(Nat.succ (Nat.succ i))) = 0 := by
        simp [Nat.pow_succ]
        norm_num
        apply Nat.div_eq_zero
        norm_num
        apply Nat.lt_of_lt_of_le
        · norm_num
        · apply Nat.le_mul_of_pos_left
          apply Nat.pow_pos
          norm_num
      rw [this] at hi
      simp at hi
