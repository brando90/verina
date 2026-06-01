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
  use [-2, -1]
constructor
simp [maxStrength_precond]
intro h_precond
simp [maxStrength_postcond]
intro h
simp [maxStrength] at h
simp [List.filter, List.foldl, List.isEmpty, List.length] at h
norm_num at h
-- h should now show that the result is -1
have h_result : maxStrength [-2, -1] h_precond = -1 := by
  simp [maxStrength, List.filter, List.foldl, List.isEmpty, List.length]
  norm_num
rw [h_result] at h
clear h_result
simp [List.sublists] at h
-- The sublists are [[-2], [-1], [-2, -1]]
-- Products are [-2, -1, 2]
-- So the result should be 2, not -1
cases h with
| intro h_contains h_all =>
  -- h_all says all products ≤ -1, but we have product 2
  have h_prod : 2 ∈ List.map (List.foldl (· * ·) 1) [[-2], [-1], [-2, -1]] := by
    simp [List.map, List.foldl]
    norm_num
  have h_le : ∀ x ∈ List.map (List.foldl (· * ·) 1) [[-2], [-1], [-2, -1]], x ≤ -1 := by
    simp [List.all] at h_all
    exact h_all
  have h_bad : 2 ≤ -1 := h_le 2 h_prod
  norm_num at h_bad
