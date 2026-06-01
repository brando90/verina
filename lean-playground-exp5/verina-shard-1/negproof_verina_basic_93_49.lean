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
simp only [SwapBitvectors_postcond, SwapBitvectors, not_and]
left
-- Show that result.fst ≠ Y
-- The implementation returns (X, Y) = (1, 2) but should return (Y, X) = (2, 1)
-- So result.fst = 1 and Y = 2, which are not equal
decide
