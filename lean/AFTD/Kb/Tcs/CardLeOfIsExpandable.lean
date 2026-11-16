import AFTD.Prelude
import AFTD.Kb.Tcs.IsExpandable

/-!
# card_le_of_is_expandable

Topic: combinatorics   Node: d90f4ac74a29

Provenance: helper lemma. arXiv:2611.16957, Section 3.1

Every expandable set in a hypergraph with edge size bound r has cardinality at most r.
-/

/-- An expandable set in a hypergraph with edge size bound r has cardinality at most r. -/
theorem card_le_of_is_expandable {V : Type*} {H : Finset (Finset V)} {r : ℕ} {X : Finset V} (hX : IsExpandable H r X) : X.card ≤ r := by
  obtain ⟨e, heH, hXe, -⟩ := hX.2.2 ∅ (Finset.disjoint_empty_left X) (by simp)
  exact le_trans (Finset.card_le_card hXe) (hX.2.1 e heH)
