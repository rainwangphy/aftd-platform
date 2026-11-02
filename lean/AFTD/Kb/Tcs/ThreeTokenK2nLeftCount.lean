import AFTD.Prelude

/-!
# three_token_k2n_left_count

Topic: graphs   Node: 7671c3bb86d6

Provenance: helper lemma. Explicit construction for three_token_k2n_has_dominating_set and OP-666.

The number of left-part vertices in a three-token configuration.
-/

noncomputable def three_token_k2n_left_count {n : ℕ}
    (z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3}) : ℕ := by
  classical
  exact (z.val.filter (fun v => ∃ i : Fin 2, v = Sum.inl i)).card
