import AFTD.Prelude
import AFTD.Kb.Physics.IsClawPacking

/-!
# max_claw_packing

Topic: quantum_mechanics   Node: 0c11177eb7dd

Provenance: formalization of a published result. Source: arXiv:2511.19585

For a simple graph G on a finite type V, max_claw_packing G is defined as the supremum of Finset.card P over all P : Finset (Finset V) in Finset.univ satisfying is_claw_packing G P.
-/

/-- The maximum number of pairwise vertex-disjoint induced claws in a finite graph. -/
noncomputable def max_claw_packing {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by classical exact Finset.sup (Finset.filter (is_claw_packing G) Finset.univ) Finset.card
