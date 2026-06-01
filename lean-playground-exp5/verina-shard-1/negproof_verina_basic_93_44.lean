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
simp only [SwapBitvectors_postcond, SwapBitvectors]
simp only [not_and, not_imp]
left
-- The implementation returns (newY, newX) where:
-- temp = X ^^^ Y = 1 ^^^ 2 = 3
-- newY = temp ^^^ Y = 3 ^^^ 2 = 1 = X
-- newX = temp ^^^ newY = 3 ^^^ 1 = 2 = Y
-- So it returns (1, 2) = (X, Y)
-- But postcondition expects result.fst = Y = 2
-- We need to show 1 ≠ 2
norm_num
