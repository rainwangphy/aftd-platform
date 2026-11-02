import AFTD.Prelude
import AFTD.Kb.Physics.IsInducedClaw

/-!
# is_claw_packing

Topic: quantum_mechanics   Node: 6ed4f35515e4

Provenance: formalization of a published result. Source: arXiv:2511.19585

For a simple graph G on type V and a finite set of finite vertex subsets P : Finset (Finset V), is_claw_packing G P asserts that every s in P satisfies is_induced_claw G s and the elements of P are pairwise disjoint.
-/

/-- A collection of pairwise vertex-disjoint induced claws in a graph. -/
def is_claw_packing {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V)) : Prop := (∀ s ∈ P, is_induced_claw G s) ∧ (P : Set (Finset V)).PairwiseDisjoint id
