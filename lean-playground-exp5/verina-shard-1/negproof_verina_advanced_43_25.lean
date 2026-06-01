import Mathlib

@[reducible, simp]
def maxStrength_precond (nums : List Int) : Prop :=
  nums ≠ []

def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  let positives := nums.filter (· > 0)
  let negatives := nums.filter (· < 0)
  let posProduct := positives.foldl (· * ·) 1
  let negProduct := negatives.foldl (· * ·) 1
  if positives.isEmpty && negatives.isEmpty then 0
  else if positives.isEmpty then
    if negatives.length % 2 = 0 then negProduct
    else negatives.foldl (fun best x => max best x) (negatives[0]!)
  else if negatives.length % 2 = 0 then posProduct * negProduct
  else
    let maxNeg := negatives.foldl max (negatives[0]!)
    posProduct * (negProduct / maxNeg)
@[reducible, simp]
def maxStrength_postcond (nums : List Int) (result : Int) (h_precond : maxStrength_precond (nums)) :=
  let sublists := nums.sublists.filter (· ≠ [])
  let products := sublists.map (List.foldl (· * ·) 1)
  products.contains result ∧ products.all (· ≤ result)

theorem maxStrength_spec_violated : ∃ nums,
    ∃ (h_precond : maxStrength_precond (nums)),
    ¬ maxStrength_postcond (nums) (maxStrength (nums) h_precond) h_precond := by
  use [-2, -3, -4]
simp only [maxStrength_precond]
intro h_precond
simp only [maxStrength_postcond]
push_neg
constructor
· -- First, show that maxStrength returns -2
  have h_result : maxStrength [-2, -3, -4] h_precond = -2 := by
    rw [maxStrength]
    simp [List.filter]
    rfl
  rw [h_result]
  -- Now show that -2 is in the products list
  simp [List.sublists, List.filter, List.map, List.foldl]
  decide
· -- Second, show that not all products are ≤ -2
  use 12
  constructor
  · -- Show that 12 is in the products list
    simp [List.sublists, List.filter, List.map, List.foldl]
    decide
  · -- Show that 12 > -2
    norm_num
