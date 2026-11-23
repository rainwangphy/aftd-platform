import AFTD.Prelude

/-!
# lattice_graph_two_one

Topic: graphs   Node: 542e92e5a12b

Provenance: formalization of a published result. Source: arXiv:2611.18633 Definition 1.1

The radius-one lattice graph G_{2,1} on ℤ² has an edge between distinct lattice points u and v if and only if |u₁ - v₁| ≤ 1 and |u₂ - v₂| ≤ 1.
-/

/-- The radius-one lattice graph G_{2,1} on ℤ × ℤ. -/
def lattice_graph_two_one : SimpleGraph (ℤ × ℤ) := {
  Adj := fun u v => u ≠ v ∧ |u.1 - v.1| ≤ 1 ∧ |u.2 - v.2| ≤ 1
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, by rw [abs_sub_comm]; exact h.2.1, by rw [abs_sub_comm]; exact h.2.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
}
