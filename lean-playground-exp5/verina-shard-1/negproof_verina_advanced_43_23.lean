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
-- The implementation returns -2
have impl_result : maxStrength [-2, -3, -4] (by simp [maxStrength_precond]) = -2 := by
  simp [maxStrength]
  simp [List.filter, List.foldl, List.length]
  norm_num
  simp [List.getElem!, List.get!]
  norm_num
-- But 12 is a valid product from sublists and 12 > -2
have twelve_product : ∃ sublist ∈ ([-2, -3, -4].sublists.filter (· ≠ [])),
                      sublist.foldl (· * ·) 1 = 12 := by
  use [-3, -4]
  constructor
  · simp [List.sublists, List.filter, List.mem_filter]
  · simp [List.foldl]
    norm_num
-- Get the contradiction
obtain ⟨contains, all_le⟩ := h
rw [impl_result] at all_le
specialize all_le 12
have twelve_in_products : 12 ∈ ([-2, -3, -4].sublists.filter (· ≠ [])).map (List.foldl (· * ·) 1) := by
  simp [List.mem_map]
  use [-3, -4]
  constructor
  · simp [List.sublists, List.filter, List.mem_filter]
  · simp [List.foldl]
    norm_num
have : 12 ≤ -2 := all_le twelve_in_products
norm_num at this
