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
simp only [allVowels, String.toList, List.all, Char.isAlpha, List.contains] at h
simp only [normalize_str, String.toList] at h
-- The implementation returns true for "aaa"
have impl_true : allVowels "aaa" trivial = true := by simp [allVowels, String.toList, List.all, Char.isAlpha, List.contains]
-- From h and impl_true, we get that the normalized "aaa" contains all vowels
have all_vowels : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v) := by
  rw [← h]
  exact impl_true
-- But ['a', 'a', 'a'] doesn't contain 'e'
have no_e : ¬ ['a', 'a', 'a'].contains 'e' := by simp [List.contains]
-- This contradicts all_vowels
simp only [List.all] at all_vowels
cases all_vowels
case cons h1 h2 =>
  cases h2
  case cons h2' h3 =>
    simp only [List.contains] at h2'
    exact no_e h2'
