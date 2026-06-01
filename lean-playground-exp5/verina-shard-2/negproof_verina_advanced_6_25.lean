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
simp only [allVowels_postcond, normalize_str] at h
-- The implementation returns true for "aaa"
have impl_true : allVowels "aaa" trivial = true := by
  unfold allVowels
  simp [String.toList, List.all, List.contains, List.elem, Char.isAlpha]
  rfl
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in "aaa".toList
have all_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) :=
  h.mp trivial
-- But "aaa".toList = ['a', 'a', 'a'], which doesn't contain 'e'
have not_e : ¬("aaa").toList.contains 'e' := by
  simp [String.toList, List.contains, List.elem]
-- This contradicts all_in
have e_in : ("aaa").toList.contains 'e' := by
  have : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) → ("aaa").toList.contains 'e' := by
    intro h_all
    simp [List.all] at h_all
    exact h_all.2.1
  exact this all_in
exact not_e e_in
