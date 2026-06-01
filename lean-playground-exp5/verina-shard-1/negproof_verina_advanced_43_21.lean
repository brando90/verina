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
use (by simp [maxStrength_precond])
simp [maxStrength_postcond]
intro h
simp [maxStrength] at h
simp [List.filter, List.foldl] at h
norm_num at h
-- h says the result is -2
have : List.sublists [-2, -3, -4] = [[], [-4], [-3], [-3, -4], [-2], [-2, -4], [-2, -3], [-2, -3, -4]] := by
  rfl
simp [List.sublists, List.filter, List.map, List.foldl] at h
norm_num at h
