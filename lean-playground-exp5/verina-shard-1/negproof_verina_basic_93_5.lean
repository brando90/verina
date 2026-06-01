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
-- h assumes the postcondition holds, we'll show contradiction
-- The implementation returns (1, 2) instead of (2, 1)
simp only [SwapBitvectors] at h
-- Evaluate the XOR operations
simp only [HXor.hXor, instHXor, UInt8.xor] at h
-- Now h contains: (1, 2).fst = 2 ∧ (1, 2).snd = 1 ∧ ...
simp at h
-- This gives us 1 = 2 ∧ 2 = 1 ∧ ...
cases h with
| intro h1 h2 =>
  -- h1 : 1 = 2, which is false
  norm_num at h1
