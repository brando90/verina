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
simp only [allVowels_postcond, normalize_str, String.toList] at h
-- The implementation returns true for "aaa"
have impl_true : allVowels "aaa" trivial = true := by
  simp only [allVowels, String.toList, List.all, List.elem, Char.isAlpha]
  decide
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in ['a', 'a', 'a']
have all_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v) :=
  h.mp trivial
-- Check that 'e' is in the vowel list
have e_in_vowels : 'e' ∈ ['a', 'e', 'i', 'o', 'u'] := by
  simp only [List.mem_cons, List.mem_singleton]
  right; left; rfl
-- From all_in and e_in_vowels, we get that 'e' should be in ['a', 'a', 'a']
rw [List.all_iff_forall] at all_in
have e_in_aaa : ['a', 'a', 'a'].contains 'e' := all_in 'e' e_in_vowels
-- But 'e' is not in ['a', 'a', 'a']
have e_not_in_aaa : ¬(['a', 'a', 'a'].contains 'e') := by
  simp only [List.contains, List.elem]
  decide
-- Contradiction
exact e_not_in_aaa e_in_aaa
