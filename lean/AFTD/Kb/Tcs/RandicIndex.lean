import AFTD.Prelude

/-!
# randic_index

Topic: graphs   Node: 0fa6487d188c

Provenance: formalization of a published result. Source: arXiv:2611.03879 Section 2.2

The Randić index of a finite simple graph G is the sum over all edges e in G of 1 / Real.sqrt (degree(u) * degree(v)) where e is the unordered pair of u and v.
-/

/-- The Randić index of a finite simple graph G is the sum over its edges of 1 / sqrt(d(u) * d(v)). -/
noncomputable def randic_index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := open scoped Classical in
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => 1 / Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)), by
    intro u v
    simp [mul_comm]⟩ e
