import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPolySingletonInduced
import AFTD.Kb.Tcs.PetrialNullityPolyIso
import AFTD.Kb.Tcs.PetrialNullityPoly

/-!
# petrial_nullity_poly_card_one_finset

Topic: combinatorics   Node: 178d1657c346

Provenance: helper lemma. Singleton finite-set base case for the OP-1239 certificate.

For every finite vertex set of cardinality one, the partial Petrial nullity polynomial of the induced graph is one plus X.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_nullity_poly_card_one_finset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (hs : s.card = 1) : petrial_nullity_poly (G.induce (s : Set V)) = 1 + Polynomial.X := by
  classical
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs
  let e : (G.induce ((({v} : Finset V)) : Set V)) ≃g G.induce ({v} : Set V) := {
    toEquiv := Equiv.subtypeEquivRight (fun x => by simp)
    map_rel_iff' := by rfl
  }
  exact (petrial_nullity_poly_iso _ _ e).trans (petrial_nullity_poly_singleton_induced G v)
