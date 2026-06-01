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
simp only [normalize_str, String.toList]
-- The implementation returns true for "a"
have impl_true : List.all ['a'] (fun c => !c.isAlpha || ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c) = true := by
  simp [List.all]
  simp [Char.isAlpha, List.contains, List.elem]
  decide
rw [impl_true]
simp only [true_iff]
-- normalize_str "a" = ['a'] after filtering alphabetic and lowercasing
have norm_eq : (List.filter Char.isAlpha ['a']).map Char.toLower = ['a'] := by
  simp [List.filter, List.map, Char.isAlpha, Char.toLower]
  decide
rw [norm_eq]
-- Now we need to show that NOT all five vowels are in ['a']
simp [List.all, List.contains, List.elem]
-- This asks if 'a', 'e', 'i', 'o', 'u' are all in ['a']
-- Only 'a' is in ['a'], so we get: True ∧ False ∧ False ∧ False ∧ False
decide
