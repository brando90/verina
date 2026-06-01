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
  use [-1, -2, -3]
simp only [maxStrength_precond]
have h_precond : [-1, -2, -3] ≠ [] := by decide
use h_precond
simp only [maxStrength_postcond]
push_neg
right
use 6
constructor
· -- Show that 6 is in the products list
  simp only [List.mem_map, List.mem_filter, List.mem_sublists]
  use [-2, -3]
  constructor
  · constructor
    · -- [-2, -3] is a sublist of [-1, -2, -3]
      decide
    · -- [-2, -3] ≠ []
      decide
  · -- Product of [-2, -3] is 6
    simp [List.foldl]
· -- Show that maxStrength returns -1 < 6
  simp only [not_le]
  -- We need to show maxStrength [-1, -2, -3] h_precond < 6
  -- First compute what maxStrength returns
  have h_result : maxStrength [-1, -2, -3] h_precond = -1 := by
    unfold maxStrength
    simp [List.filter, List.isEmpty, List.length, List.foldl, max]
    native_decide
  rw [h_result]
  norm_num
