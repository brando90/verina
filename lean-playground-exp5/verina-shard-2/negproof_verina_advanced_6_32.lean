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
-- The implementation returns true for "aaa" since all chars are vowels
have impl_true : allVowels "aaa" trivial = true := by
  rfl
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in normalize_str "aaa"
have all_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str "aaa").contains v) :=
  h.mp trivial
-- But normalize_str "aaa" = ['a', 'a', 'a'], which doesn't contain 'e'
have not_e : ¬(normalize_str "aaa").contains 'e' := by
  simp only [normalize_str, String.toList, List.contains, List.elem]
  decide
-- This contradicts all_in
simp only [List.all] at all_in
have e_in : (normalize_str "aaa").contains 'e' := all_in.2.1
exact not_e e_in
