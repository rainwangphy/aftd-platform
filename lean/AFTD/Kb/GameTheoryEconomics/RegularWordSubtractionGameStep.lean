import AFTD.Prelude

/-!
# regular_word_subtraction_game_step

Topic: combinatorial_games   Node: fcf2706980f5

Provenance: helper lemma. step towards op_1677_regular_word_subtraction_state_complexity_ge

The transition function of the subtraction DFA regular_word_subtraction_language N hN, exposed as a standalone function on Fin (N + 1): false sends 0 to 2 and cycles 1 through N, true sends 0 to 1, swaps 1 and 2, and fixes 3 through N.
-/

/-- The step function of the subtraction DFA for regular_word_subtraction_language, on state type Fin (N+1). -/
noncomputable def regular_word_subtraction_game_step (N : ℕ) (hN : 3 ≤ N) : Fin (N + 1) → Bool → Fin (N + 1) := fun (q : Fin (N + 1)) (c : Bool) =>
  match c with
  | false =>
    if h0 : q.val = 0 then ⟨2, by omega⟩
    else if hNeq : q.val = N then ⟨1, by omega⟩
    else ⟨q.val + 1, by have := q.isLt; omega⟩
  | true =>
    if h0 : q.val = 0 then ⟨1, by omega⟩
    else if h1 : q.val = 1 then ⟨2, by omega⟩
    else if h2 : q.val = 2 then ⟨1, by omega⟩
    else q
