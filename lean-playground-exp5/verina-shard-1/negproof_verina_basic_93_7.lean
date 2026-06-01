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
intro h
-- The postcondition requires result.fst = Y and result.snd = X
-- But the implementation returns (newY, newX) where newY = X and newX = Y
-- So it returns (X, Y) = (1, 2) instead of (Y, X) = (2, 1)
have h_fst : (SwapBitvectors 1 2 trivial).fst = 1 := by
  unfold SwapBitvectors
  simp
have h_snd : (SwapBitvectors 1 2 trivial).snd = 2 := by
  unfold SwapBitvectors
  simp
-- h.1 says result.fst = Y = 2, but we showed result.fst = 1
rw [h_fst] at h
simp at h
