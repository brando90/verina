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
  use 1, 2
use trivial
simp only [SwapBitvectors_postcond]
intro h
-- Compute what SwapBitvectors returns
have : SwapBitvectors 1 2 trivial = (1, 2) := by
  unfold SwapBitvectors
  rfl
rw [this] at h
-- h now states (1, 2).fst = 2 ∧ (1, 2).snd = 1 ∧ ...
-- But (1, 2).fst = 1 and (1, 2).snd = 2
obtain ⟨h1, _, _⟩ := h
-- h1 : (1, 2).fst = 2
-- But (1, 2).fst = 1
have : (1 : UInt8) = 2 := h1
-- This is false
decide
