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
intro h_post
-- The specification states that for invalid digits, result should be []
-- '1' is not in ['2','3','4','5','6','7','8','9']
have h_not_empty : ¬"1".isEmpty := by
  simp [String.isEmpty, String.toList]
have h_invalid : "1".toList.any (fun c => ¬(c ∈ ['2', '3', '4', '5', '6', '7', '8', '9'])) := by
  simp [String.toList, List.any, List.mem_cons, List.mem_singleton]
  decide
-- From the postcondition, with invalid digit, result should be []
unfold letterCombinations_postcond at h_post
simp [h_not_empty, h_invalid] at h_post
-- h_post now states: letterCombinations "1" trivial = []
-- But let's check what the implementation actually returns
have h_impl : letterCombinations "1" trivial = [""] := by
  unfold letterCombinations
  simp [String.toList]
  -- The combine function starts with acc = [""] and processes ['1']
  -- Since '1' is not in mapping, it returns acc unchanged
  rfl
-- This gives us [""] = [], which is a contradiction
rw [h_impl] at h_post
-- [""] ≠ []
exact List.cons_ne_nil "" [] h_post
