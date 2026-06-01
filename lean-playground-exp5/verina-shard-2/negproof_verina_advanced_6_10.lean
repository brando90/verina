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
-- Compute what the implementation returns
have impl_result : allVowels "aaa" trivial = true := by
  simp only [allVowels]
  simp only [String.toList, List.all, Char.isAlpha, List.contains]
  decide
-- Apply the implementation result to h
rw [impl_result] at h
-- Now h states that all five vowels are in ['a', 'a', 'a']
simp only [String.toList] at h
-- But ['a', 'a', 'a'] doesn't contain 'e'
have no_e : ¬(['a', 'a', 'a'].contains 'e') := by
  simp only [List.contains, List.elem]
  decide
-- From h, we get that ['a', 'a', 'a'] contains 'e'
have yes_e : ['a', 'a', 'a'].contains 'e' := by
  rw [List.all_iff_forall] at h
  apply h
  simp
-- Contradiction
exact no_e yes_e
