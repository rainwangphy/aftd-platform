import AFTD.Prelude
import AFTD.Kb.Tcs.CompatibleLabelings

/-!
# compatible_labelings_empty

Topic: online_algorithms   Node: 14585ecef5c8

Provenance: helper lemma. arXiv:2611.13571, Section 5.1

For any simple graph G on vertex set Fin n with decidable adjacency, compatible_labelings G ∅ = Nat.factorial n.
-/

/-- The number of compatible labelings for the empty observed edge set is n!. -/
theorem compatible_labelings_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    compatible_labelings G ∅ = Nat.factorial n := by
  unfold compatible_labelings
  simp [Fintype.card_perm]
