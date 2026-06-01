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
push_neg
left
-- We need to show that the first component is not Y
-- The implementation computes:
-- temp = 1 ^^^ 2 = 3
-- newY = 3 ^^^ 2 = 1
-- newX = 3 ^^^ 1 = 2
-- So it returns (1, 2) = (X, Y)
-- But the postcondition expects result.fst = Y = 2
-- So we need to show 1 ≠ 2
simp [UInt8.xor_comm, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
