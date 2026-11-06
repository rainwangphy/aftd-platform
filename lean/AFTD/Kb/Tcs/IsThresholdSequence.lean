import AFTD.Prelude

/-!
# is_threshold_sequence

Topic: graphs   Node: 16f5a6d8b761

Provenance: formalization of a published result. Source: arXiv:2611.02191 Sec. 11.2; Chvátal and Hammer (1977)

A degree sequence d on n vertices is a threshold degree sequence if there exists a simple graph G on n vertices with degree sequence d having no induced 2K_2, C_4, or P_4.
-/

/-- A degree sequence d on Fin n is a threshold degree sequence if it is realized by a simple graph with no induced 2K₂, C₄, or P₄. -/
def is_threshold_sequence {n : ℕ} (d : Fin n → ℕ) : Prop := open scoped Classical in
  ∃ G : SimpleGraph (Fin n),
    (∀ a b c d : Fin n, [a, b, c, d].Nodup →
      ¬ (G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∧
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d)) ∧
    ∀ v : Fin n, G.degree v = d v
