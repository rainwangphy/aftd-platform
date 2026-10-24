import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdditiveColoring

/-!
# is_additive_coloring_le_iff

Topic: graphs   Node: 758f2044c241

Provenance: helper lemma. folklore

A vertex labeling f on a finite graph G is an additive coloring bounded by k if and only if 1 ≤ f(v) ≤ k for all vertices v and adjacent vertices have distinct neighborhood sums.
-/

/-- Equivalence between the is_additive_coloring predicate with an upper bound and the explicit bounded neighborhood sum condition. -/
lemma is_additive_coloring_le_iff
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) (k : ℕ) :
    (is_additive_coloring G f ∧ ∀ v, f v ≤ k) ↔
    (∀ v, 1 ≤ f v ∧ f v ≤ k) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w) := by
  unfold is_additive_coloring
  constructor
  · rintro ⟨⟨hpos, hadj⟩, hle⟩
    exact ⟨fun v => ⟨hpos v, hle v⟩, hadj⟩
  · rintro ⟨h1, hadj⟩
    exact ⟨⟨fun v => (h1 v).1, hadj⟩, fun v => (h1 v).2⟩
