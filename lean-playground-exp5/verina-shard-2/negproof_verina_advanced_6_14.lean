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
-- The implementation returns true for "aaa" because all characters are vowels
have impl_true : allVowels "aaa" trivial = true := by
  rfl
-- Apply this to our hypothesis
rw [impl_true] at h
-- Now h says: true ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str "aaa").contains v)
-- Simplify normalize_str "aaa"
simp only [normalize_str, String.toList] at h
-- From the forward direction, we get that all five vowels should be in ['a', 'a', 'a']
have all_vowels_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ['a', 'a', 'a'].contains v) := by
  exact h.mp trivial
-- But 'e' is not in ['a', 'a', 'a']
have e_not_in : ¬(['a', 'a', 'a'].contains 'e') := by
  decide
-- From all_vowels_in, 'e' should be in the list
have e_in : ['a', 'a', 'a'].contains 'e' := by
  have : ∀ v ∈ ['a', 'e', 'i', 'o', 'u'], ['a', 'a', 'a'].contains v := by
    rwa [List.all_iff_forall] at all_vowels_in
  apply this
  simp
-- Contradiction
exact e_not_in e_in
