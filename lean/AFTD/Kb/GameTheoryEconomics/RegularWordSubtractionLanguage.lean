import AFTD.Prelude

/-!
# regular_word_subtraction_language

Topic: combinatorial_games   Node: 4bf297c11437

Provenance: original. Related work: arXiv:2611.09157

For each integer N ≥ 3, regular_word_subtraction_language N hN is the language over Bool accepted by the DFA with state set Fin (N + 1), start state 0, and sole accepting state 2, where letter false sends 0 to 2 and cyclically permutes 1 through N, and letter true sends 0 to 1, swaps 1 and 2, and fixes 3 through N.
-/

/-- The regular language accepted by the N-state binary DFA A_N of OP-1677. -/
def regular_word_subtraction_language (N : ℕ) (hN : 3 ≤ N) : Language Bool := (DFA.mk
  (fun (q : Fin (N + 1)) (c : Bool) =>
    match c with
    | false =>
      if h0 : q.val = 0 then ⟨2, by omega⟩
      else if hN_eq : q.val = N then ⟨1, by omega⟩
      else ⟨q.val + 1, by have := q.isLt; omega⟩
    | true =>
      if h0 : q.val = 0 then ⟨1, by omega⟩
      else if h1 : q.val = 1 then ⟨2, by omega⟩
      else if h2 : q.val = 2 then ⟨1, by omega⟩
      else q)
  ⟨0, by omega⟩
  {⟨2, by omega⟩}).accepts
