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
-- The function returns (X, Y) instead of (Y, X)
have calc_result : SwapBitvectors 1 2 trivial = (1, 2) := by
  unfold SwapBitvectors
  -- temp = 1 ^^^ 2 = 3
  -- newY = 3 ^^^ 2 = 1
  -- newX = 3 ^^^ 1 = 2
  -- result = (1, 2)
  rfl
rw [calc_result] at h
-- h says that (1, 2).fst = 2, but (1, 2).fst = 1
cases h with
| intro h_fst h_rest =>
  -- h_fst : (1, 2).fst = 2
  -- But (1, 2).fst = 1
  norm_num at h_fst
