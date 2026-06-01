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
  use [-3, -2, -1]
use (by simp [maxStrength_precond] : maxStrength_precond [-3, -2, -1])
simp [maxStrength_postcond]
push_neg
-- Compute what maxStrength returns
have h_result : maxStrength [-3, -2, -1] _ = -1 := by
  simp [maxStrength]
  simp [List.filter, List.foldl, List.isEmpty, List.length]
  norm_num
  simp [List.getElem!]
  rfl
rw [h_result]
-- Show that either -1 is not in products or there exists a product > -1
right
use 6
constructor
· -- Show 6 is in the products
  simp [List.sublists, List.map, List.foldl]
  right; right; right; left
  norm_num
· -- Show 6 > -1
  norm_num
