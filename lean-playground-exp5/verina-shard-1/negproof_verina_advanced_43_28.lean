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
simp only [maxStrength_postcond]
push_neg
-- We need to show that either the result is not in products OR not all products ≤ result
-- We'll show the second: there exists a product > result
right
use 12
constructor
· -- Show that 12 is in the products list
  simp only [List.mem_map, List.mem_filter]
  use [-3, -4]
  constructor
  · -- Show [-3, -4] is a non-empty sublist
    constructor
    · -- [-3, -4] is a sublist of [-2, -3, -4]
      simp only [List.mem_sublists]
      decide
    · -- [-3, -4] ≠ []
      decide
  · -- Show the product of [-3, -4] is 12
    simp only [List.foldl]
    norm_num
· -- Show that maxStrength returns -2 < 12
  have h_result : maxStrength [-2, -3, -4] (by simp [maxStrength_precond]) = -2 := by
    rw [maxStrength]
    simp only [List.filter, List.isEmpty, List.length, List.foldl, List.getElem!, List.get!]
    -- positives = [], negatives = [-2, -3, -4]
    -- negatives.length = 3, which is odd
    -- So we go to the else branch that computes max of negatives
    simp only [max, decide_eq_true_eq, ite_eq_right_iff]
    intros
    decide
  rw [h_result]
  norm_num
