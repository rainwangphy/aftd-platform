import AFTD.Prelude

/-!
# retained_line_truncate

Topic: algorithms   Node: 7929a5716ff5

Provenance: helper lemma. OP-815: truncation of the retained line graph by edge length.

The graph on the same line vertices formed by retaining exactly those edges of the given graph whose endpoint distance is at most k.
-/

noncomputable def retained_line_truncate {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : SimpleGraph (Fin n) := {
  Adj v w := G.Adj v w ∧ Nat.dist v.val w.val ≤ k
  symm := by constructor; intro v w h; exact ⟨h.1.symm, by simpa [Nat.dist_comm] using h.2⟩
  loopless := by constructor; intro v h; exact G.irrefl h.1
}
