@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  True

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x2 := Y - X
  let y2 := Y - x2
  let x3 := y2 + x2 - y2 + x2
  (x2 + y2 - x2, y2)
@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result : (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem SwapArithmetic_spec_violated : ∃ X Y,
    ∃ (h_precond : SwapArithmetic_precond (X) (Y)),
    ¬ SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  use 1, 2, trivial
unfold SwapArithmetic_postcond SwapArithmetic
simp [not_and_or]
left
norm_num
