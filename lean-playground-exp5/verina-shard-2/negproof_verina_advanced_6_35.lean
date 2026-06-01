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
unfold allVowels_postcond
simp only [allVowels]
-- The implementation returns true for "a"
have impl_result : (let vowels := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']
                    ("a").toList.all (fun c => !c.isAlpha || vowels.contains c)) = true := by
  simp [String.toList, List.all, List.contains, List.elem, Char.isAlpha]
  decide
simp [impl_result]
-- Now we need to show that not all vowels are in normalize_str "a"
intro h
-- From h, all vowels must be in normalize_str "a"
have all_vowels_in : List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str "a").contains v) := h
-- But normalize_str "a" = ['a']
have norm_eq : normalize_str "a" = ['a'] := by
  unfold normalize_str
  simp [String.toList]
rw [norm_eq] at all_vowels_in
-- This says all five vowels are in the list ['a'], which is false
simp [List.all, List.contains, List.elem] at all_vowels_in
-- Extract that 'e' must be in ['a']
have e_in : 'e' ∈ ['a'] := all_vowels_in.2.1
-- But 'e' is not in ['a']
simp at e_in
