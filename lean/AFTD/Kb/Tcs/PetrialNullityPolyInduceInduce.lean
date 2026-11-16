import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialNullityPolyIso

/-!
# petrial_nullity_poly_induce_induce

Topic: combinatorics   Node: 3dfc3734b15d

Provenance: helper lemma. Induced-subgraph bookkeeping for the OP-1239 candidate.

The nullity polynomial obtained by inducing on s and then on vertices in t equals the polynomial of the graph induced on the intersection of s and t.
-/

theorem petrial_nullity_poly_induce_induce {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Set V) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] : petrial_nullity_poly ((G.induce s).induce {x : s | (x : V) ∈ t}) = petrial_nullity_poly (G.induce (s ∩ t)) := by
  classical
  apply petrial_nullity_poly_iso
  exact {
    toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)
    map_rel_iff' := by rfl
  }
