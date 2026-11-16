import AFTD.Prelude

/-!
# regular_word_subtraction_dfa_three

Topic: combinatorial_games   Node: df421ec2b072

Provenance: helper lemma. step towards op_1677_regular_word_subtraction_base_case_three

An explicit 8-state DFA over Bool with state set Fin 8, start state 0, and accepting states {1, 4, 6, 7}, recognizing the winning positions in the normal word subtraction game for N = 3.
-/

/-- Explicit 8-state DFA over Bool recognizing winning positions in the word subtraction game for N = 3. -/
def regular_word_subtraction_dfa_three : DFA Bool (Fin 8) := DFA.mk
  (fun (q : Fin 8) (c : Bool) =>
    match q.val, c with
    | 0, false => ⟨1, by omega⟩
    | 0, true  => ⟨2, by omega⟩
    | 1, false => ⟨3, by omega⟩
    | 1, true  => ⟨2, by omega⟩
    | 2, false => ⟨1, by omega⟩
    | 2, true  => ⟨4, by omega⟩
    | 3, false => ⟨4, by omega⟩
    | 3, true  => ⟨5, by omega⟩
    | 4, false => ⟨6, by omega⟩
    | 4, true  => ⟨4, by omega⟩
    | 5, false => ⟨4, by omega⟩
    | 5, true  => ⟨7, by omega⟩
    | 6, false => ⟨5, by omega⟩
    | 6, true  => ⟨5, by omega⟩
    | 7, _     => ⟨7, by omega⟩
    | _, _     => ⟨0, by omega⟩)
  ⟨0, by omega⟩
  {⟨1, by omega⟩, ⟨4, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩}
