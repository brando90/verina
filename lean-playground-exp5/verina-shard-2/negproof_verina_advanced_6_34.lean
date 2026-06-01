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
  use "a"
use trivial
intro h
simp only [allVowels_postcond] at h
-- The implementation returns true for "a" since 'a' is a vowel
have impl_true : allVowels "a" trivial = true := by
  unfold allVowels
  simp [String.toList, List.all, Char.isAlpha]
  decide
-- From the biconditional and impl_true, we get that all five vowels must be in normalize_str "a"
rw [impl_true] at h
have all_five : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str "a").contains v) :=
  h.mp trivial
-- But normalize_str "a" = ['a'], so 'e' is not contained
have norm_a : normalize_str "a" = ['a'] := by
  unfold normalize_str
  simp [String.toList]
rw [norm_a] at all_five
-- Now check that 'e' ∈ ['a'] is false
have e_not_in : ¬('e' ∈ ['a']) := by
  simp
-- But all_five says 'e' must be in ['a']
simp [List.all, List.contains, List.elem] at all_five
obtain ⟨_, he, _, _, _⟩ := all_five
exact e_not_in he
