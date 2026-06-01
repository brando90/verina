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
use (by simp [maxStrength_precond] : maxStrength_precond [-2, -3, -4])
simp [maxStrength_postcond]
push_neg
right
use 12
constructor
· -- Show that 12 is in the products list
  simp [List.mem_map]
  use [-3, -4]
  constructor
  · simp [List.mem_filter, List.sublists]
    decide
  · simp [List.foldl]
    norm_num
· -- Show that the implementation returns -2
  have h_impl : maxStrength [-2, -3, -4] (by simp [maxStrength_precond]) = -2 := by
    simp [maxStrength]
    simp [List.filter, List.foldl, List.length, List.getElem!, List.get!]
    decide
  rw [h_impl]
  norm_num
