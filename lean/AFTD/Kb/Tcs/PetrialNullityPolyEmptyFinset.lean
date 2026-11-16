import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPolyEmptyInduced
import AFTD.Kb.Tcs.PetrialNullityPolyIso
import AFTD.Kb.Tcs.PetrialNullityPoly

/-!
# petrial_nullity_poly_empty_finset

Topic: combinatorics   Node: afa3a6f1c3a1

Provenance: helper lemma. Empty finite-set base case for the OP-1239 certificate.

The partial Petrial nullity polynomial of the graph induced on the empty finite vertex set is one.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_nullity_poly_empty_finset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : petrial_nullity_poly (G.induce (((∅ : Finset V)) : Set V)) = 1 := by
  classical
  let e : (G.induce (((∅ : Finset V)) : Set V)) ≃g G.induce (∅ : Set V) := {
    toEquiv := Equiv.subtypeEquivRight (fun x => by simp)
    map_rel_iff' := by rfl
  }
  exact (petrial_nullity_poly_iso _ _ e).trans (petrial_nullity_poly_empty_induced G)
