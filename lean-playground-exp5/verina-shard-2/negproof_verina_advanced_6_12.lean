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
  simp only [allVowels, String.toList, List.all, Char.isAlpha, List.contains]
  decide
-- Apply this to our hypothesis
rw [impl_true] at h
-- Now h says: true ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v)
-- This means all five vowels should be in ['a', 'a', 'a']
simp only [String.toList] at h
-- But ['a', 'a', 'a'] doesn't contain 'e'
have no_e : ¬(['a', 'a', 'a'].contains 'e') := by
  simp only [List.contains, List.elem]
  decide
-- From h (after simplification), we need all vowels to be contained
have : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v) := by
  exact h.mp trivial
-- This means 'e' should be contained
have yes_e : ['a', 'a', 'a'].contains 'e' := by
  simp only [List.all] at this
  exact this.2.1
-- Contradiction
exact no_e yes_e
