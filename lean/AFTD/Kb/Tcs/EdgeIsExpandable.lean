import AFTD.Prelude
import AFTD.Kb.Tcs.IsExpandable

/-!
# edge_is_expandable

Topic: combinatorics   Node: 83f6225e4e87

Provenance: helper lemma. arXiv:2611.16957, Section 3.1

Every nonempty edge in a hypergraph where all edges have size at most r is expandable.
-/

/-- Every nonempty edge of a hypergraph with edge sizes at most r is expandable. -/
theorem edge_is_expandable {V : Type*} {H : Finset (Finset V)} {r : ℕ} {e : Finset V} (he : e ∈ H) (hne : e.Nonempty) (hr : ∀ f ∈ H, f.card ≤ r) : IsExpandable H r e := by
  refine ⟨hne, hr, fun Y hdisj _ => ⟨e, he, subset_rfl, hdisj.symm⟩⟩
