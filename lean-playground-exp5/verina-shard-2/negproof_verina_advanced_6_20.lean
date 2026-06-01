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
  use "aaa"
use trivial
intro h
simp only [allVowels_postcond] at h
-- The implementation returns true for "aaa"
have impl_true : allVowels "aaa" trivial = true := by
  unfold allVowels
  simp [String.toList]
  decide
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in the normalized "aaa"
simp only [normalize_str] at h
have all_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) :=
  h.mp trivial
-- But this is false because 'e' is not in "aaa"
have not_e : ¬(("aaa").toList.contains 'e') := by
  simp [String.toList, List.contains, List.elem]
  decide
-- From List.all being true, 'e' should be contained
have contains_e : ("aaa").toList.contains 'e' := by
  have h_all := all_in
  simp [List.all] at h_all
  exact h_all.2.1
-- Contradiction
exact not_e contains_e
