def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower

@[reducible, simp]
def allVowels_precond (s : String) : Prop :=
  True

def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let vowels := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']
  s.toList.all (fun c => !c.isAlpha || vowels.contains c)
@[reducible, simp]
def allVowels_postcond (s : String) (result : Bool) (h_precond : allVowels_precond (s)) :=
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

theorem allVowels_spec_violated : ∃ s,
    ∃ (h_precond : allVowels_precond (s)),
    ¬ allVowels_postcond (s) (allVowels (s) h_precond) h_precond := by
  use "a"
use trivial
unfold allVowels_postcond allVowels
simp only [String.toList]
-- Show implementation returns true
have impl_true : List.all ['a'] (fun c => !c.isAlpha || ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c) = true := by
  rfl
rw [impl_true]
simp only [true_iff]
-- Show postcondition requires all 5 vowels but only 'a' is present
unfold normalize_str
simp only [String.toList, List.filter, List.map, Char.isAlpha, Char.toLower]
-- normalize_str "a" = ['a']
-- Need to show NOT (all vowels in ['a'])
simp only [List.all, List.contains, List.elem]
-- This becomes: 'a' ∈ ['a'] ∧ 'e' ∈ ['a'] ∧ 'i' ∈ ['a'] ∧ 'o' ∈ ['a'] ∧ 'u' ∈ ['a']
-- Which simplifies to: True ∧ False ∧ False ∧ False ∧ False = False
rfl
