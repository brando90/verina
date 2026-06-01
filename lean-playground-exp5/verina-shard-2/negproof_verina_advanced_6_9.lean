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
-- The implementation returns true for "aaa" because all characters are vowels
have impl_true : allVowels "aaa" trivial = true := by
  simp only [allVowels, String.toList, List.all, Char.isAlpha, List.contains]
  decide
-- From h, we have that true ↔ all vowels are in "aaa"
rw [impl_true] at h
simp at h
-- h now states that ['a', 'a', 'a'] contains all of 'a', 'e', 'i', 'o', 'u'
-- But clearly ['a', 'a', 'a'] doesn't contain 'e'
have no_e : ¬(['a', 'a', 'a'].contains 'e') := by
  simp only [List.contains, List.elem]
  decide
-- From h, we know all vowels are contained, including 'e'
have : ['a', 'a', 'a'].contains 'e' := by
  have : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v) := h
  simp only [List.all] at this
  exact this.2.1
-- Contradiction
exact no_e this
