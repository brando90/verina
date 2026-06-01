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
unfold allVowels_postcond allVowels
simp only [String.toList]
-- The implementation returns true for "a"
have impl_true : List.all ['a'] (fun c => !c.isAlpha || ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c) = true := by
  simp [List.all, Char.isAlpha, List.contains, List.elem]
  rfl
rw [impl_true]
simp only [true_iff]
-- Now show that NOT all five vowels are in normalize_str "a"
have norm_a : normalize_str "a" = ['a'] := by
  unfold normalize_str
  simp [String.toList, List.filter, Char.isAlpha, Char.toLower]
  rfl
rw [norm_a]
-- We need to show that NOT (all five vowels are in ['a'])
simp [List.all]
-- This expands to checking if all of 'a', 'e', 'i', 'o', 'u' are in ['a']
-- Only 'a' is in ['a'], so we get a conjunction with False
simp [List.contains, List.elem]
