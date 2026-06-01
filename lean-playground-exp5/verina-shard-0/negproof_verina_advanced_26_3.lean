def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []

@[reducible, simp]
def letterCombinations_precond (digits : String) : Prop :=
  True

def letterCombinations (digits : String) (h_precond : letterCombinations_precond (digits)) : List String :=
  let mapping : List (Char × String) := [('2', "abc"), ('3', "def"), ('4', "ghi"), ('5', "jkl"), ('6', "mno"), ('7', "pqrs"), ('8', "tuv"), ('9', "wxyz")]
  let chars := digits.toList
  if chars.isEmpty then []
  else
    let rec combine (ds : List Char) (acc : List String) : List String :=
      match ds with
      | [] => acc
      | d :: rest =>
        match mapping.find? (fun (k, _) => k = d) with
        | none => combine rest acc
        | some (_, letters) =>
          let newAcc := acc.bind (fun s => letters.toList.map (fun c => s ++ String.mk [c]))
          combine rest newAcc
    combine chars [""]
@[reducible, simp]
def letterCombinations_postcond (digits : String) (result : List String) (h_precond : letterCombinations_precond (digits)) :=
  if digits.isEmpty then
    result = []
  else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then
    result = []
  else
    let expected := digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]
    result.length = expected.length ∧ result.all (λ s => s ∈ expected) ∧ expected.all (λ s => s ∈ result)

theorem letterCombinations_spec_violated : ∃ digits,
    ∃ (h_precond : letterCombinations_precond (digits)),
    ¬ letterCombinations_postcond (digits) (letterCombinations (digits) h_precond) h_precond := by
  use "1"
use trivial
unfold letterCombinations_postcond
simp only [String.isEmpty, String.toList, List.isEmpty, ite_false]
-- "1" contains an invalid digit
have h_invalid : List.any ['1'] (fun c => ¬(c ∈ ['2', '3', '4', '5', '6', '7', '8', '9'])) = true := by
  simp [List.any, List.elem]
  norm_num
-- The postcondition requires [] when there's an invalid digit
simp [h_invalid, ite_true]
-- But the implementation returns [""]
have h_impl : letterCombinations "1" trivial = [""] := by
  unfold letterCombinations
  simp [String.toList]
  -- The combine function with input ['1'] and acc [""]
  -- Since '1' is not in the mapping, it returns acc unchanged
  rfl
rw [h_impl]
-- [""] ≠ []
norm_num
