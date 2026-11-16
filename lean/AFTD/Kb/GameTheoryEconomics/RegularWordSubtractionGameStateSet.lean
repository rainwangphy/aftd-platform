import AFTD.Prelude

/-!
# regular_word_subtraction_game_state_set

Topic: combinatorial_games   Node: 74f8d0a2b3eb

Provenance: helper lemma. step towards op_1677_regular_word_subtraction_state_complexity_ge

The candidate reachable-state set R0 = {∅} ∪ {S ⊆ {1,...,N} : S meets {1,2,3}} of the subset construction for the winning-position language.
-/

/-- R0: the empty set together with all subsets of {1,...,N} meeting {1,2,3}. -/
noncomputable def regular_word_subtraction_game_state_set (N : ℕ) (hN : 3 ≤ N) : Finset (Finset (Fin (N + 1))) := insert ∅ ((((Finset.univ : Finset (Fin (N + 1))) \ {⟨0, by omega⟩}).powerset).filter
      (fun S => (S ∩ ({⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin (N + 1)))).Nonempty))
