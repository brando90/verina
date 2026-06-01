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
-- The implementation returns (newY, newX) where newY = X and newX = Y
-- So it returns (X, Y) = (1, 2) instead of (Y, X) = (2, 1)
have result_eq : SwapBitvectors 1 2 trivial = (1, 2) := by
  unfold SwapBitvectors
  simp [HXor.hXor, Xor.xor, UInt8.xor]
  norm_num
rw [result_eq] at h
-- h.1 says result.fst = Y = 2, but result.fst = 1
have h1 := h.1
norm_num at h1
