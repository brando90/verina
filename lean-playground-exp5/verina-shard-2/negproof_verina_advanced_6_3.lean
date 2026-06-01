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
-- The implementation returns true for "aaa" since it only contains vowels
have impl_true : allVowels "aaa" trivial = true := by
  unfold allVowels
  simp [String.toList, List.all, Char.isAlpha]
  rfl
-- But the postcondition requires it to contain all vowels
unfold allVowels_postcond at h
simp [normalize_str] at h
rw [impl_true] at h
simp at h
-- Show that "aaa" doesn't contain all vowels
have not_all_vowels : ¬List.all ['a', 'e', 'i', 'o', 'u'] (fun v => ("aaa").toList.contains v) := by
  simp [List.all, String.toList, List.contains]
  exists 'e'
  simp
exact not_all_vowels h
