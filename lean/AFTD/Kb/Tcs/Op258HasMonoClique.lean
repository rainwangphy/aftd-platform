import AFTD.Prelude

/-!
# op_258_has_mono_clique

Topic: combinatorics   Node: b80b0fec555e

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

The colouring c of the edges of K_n has a monochromatic K_k: there are a k-element vertex set s and a colour i such that every edge inside s has colour i.
-/

/-- The colouring `c` of the edges of the complete graph on `Fin n` admits a monochromatic `K_k`: a `k`-element vertex set all of whose edges carry one colour. -/
def op_258_has_mono_clique (n : ℕ) (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (k : ℕ) : Prop := ∃ (s : Finset (Fin n)) (i : ℕ+), s.card = k ∧
    ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → (h : u ≠ v) →
      c ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = i
