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
  simp [String.toList, List.all, List.elem, Char.isAlpha]
  decide
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in "aaa".toList
have all_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) :=
  h.mp trivial
-- But "aaa".toList = ['a', 'a', 'a'], which doesn't contain 'e'
have not_all : ¬List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) := by
  simp [List.all, String.toList, List.contains, List.elem]
  decide
-- Contradiction
exact not_all all_in
