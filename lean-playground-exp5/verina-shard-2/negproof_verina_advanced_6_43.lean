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
-- The implementation returns true for "a"
have impl_true : (String.toList "a").all (fun c => !c.isAlpha || ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c) = true := by
  simp [String.toList, List.all, Char.isAlpha, List.contains, List.elem]
  rfl
simp [impl_true]
-- Now we need to show that not all five vowels are in normalize_str "a"
intro h
-- h says all five vowels are in normalize_str "a"
have norm_a : normalize_str "a" = ['a'] := by
  unfold normalize_str
  simp [String.toList, String.data, List.filter, Char.isAlpha, Char.toLower]
  rfl
rw [norm_a] at h
-- h now says all five vowels are in ['a']
simp [List.all] at h
-- Extract that 'e' must be in ['a']
have he : List.contains ['a'] 'e' := h.2.1
-- But 'e' is not in ['a']
simp [List.contains, List.elem] at he
