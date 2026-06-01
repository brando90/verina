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
-- The postcondition states result.fst = Y ∧ result.snd = X
-- But the implementation returns (newY, newX) = (X, Y) = (1, 2)
-- So we need to show that (1, 2).fst = 2 is false
have : (SwapBitvectors 1 2 trivial).fst = 1 := by
  unfold SwapBitvectors
  simp [UInt8.xor_self, UInt8.xor_zero]
have h1 : (SwapBitvectors 1 2 trivial).fst = 2 := h.1
rw [this] at h1
norm_num at h1
