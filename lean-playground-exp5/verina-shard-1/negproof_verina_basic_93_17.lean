@[reducible, simp]
def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  True

def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  let temp := X ^^^ Y
  let newY := temp ^^^ Y
  let newX := temp ^^^ newY
  (newY, newX)
@[reducible, simp]
def SwapBitvectors_postcond (X : UInt8) (Y : UInt8) (result : UInt8 × UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem SwapBitvectors_spec_violated : ∃ X Y,
    ∃ (h_precond : SwapBitvectors_precond (X) (Y)),
    ¬ SwapBitvectors_postcond (X) (Y) (SwapBitvectors (X) (Y) h_precond) h_precond := by
  use 1, 2, trivial
simp only [SwapBitvectors_postcond]
intro h
-- The function returns (1, 2) instead of (2, 1)
have result_eq : SwapBitvectors 1 2 trivial = (1, 2) := by
  unfold SwapBitvectors
  simp [HXor.hXor, Xor.xor, UInt8.xor]
  rfl
rw [result_eq] at h
-- h now says (1, 2).fst = 2 ∧ (1, 2).snd = 1 ∧ ...
-- But (1, 2).fst = 1 and (1, 2).snd = 2
obtain ⟨h_fst, _, _⟩ := h
-- h_fst : (1, 2).fst = 2
-- This is false since (1, 2).fst = 1
simp at h_fst
