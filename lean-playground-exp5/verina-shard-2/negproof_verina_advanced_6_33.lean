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
have impl_true : allVowels "a" trivial = true := rfl
-- Apply this to our hypothesis
rw [impl_true] at h
-- From h.mp, we get that all five vowels should be in normalize_str "a"
have all_five : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str "a").contains v) :=
  h.mp trivial
-- But normalize_str "a" = ['a'], which only contains 'a'
have norm_a : normalize_str "a" = ['a'] := rfl
rw [norm_a] at all_five
-- Now all_five says all five vowels are in ['a'], which is clearly false
simp only [List.all, List.contains, List.elem, decide_eq_true_eq] at all_five
-- Extract that 'e' should be in ['a']
cases all_five with
| mk ha rest =>
  cases rest with
  | mk he rest2 =>
    -- he says 'e' = 'a' ∨ False
    simp at he
