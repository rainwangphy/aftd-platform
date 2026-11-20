import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyExternalIncidenceBudget
import AFTD.Kb.Tcs.BridgeFamilyRefinedWalkBudget

/-!
# bridge_family_refined_incidence_and_walk_budget

Topic: graphs   Node: 8d9bd9badde6

Provenance: helper lemma. OP-1957 refinement of the strict bridge-family three-walk count.

In the saturated-twin bridge-family configuration, target vertices with at least four internal neighbors account for at least two incidences per endpoint and at least four missing padded walks each.
-/

theorem bridge_family_refined_incidence_and_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L : ℕ) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card*(Q z).card) :
    let T := C.filter (fun q => 4 ≤ ((H.neighborFinset q) ∩ S).card)
    2*C.card ≤ (d-4)*T.card ∧ L*C.card + 4*T.card ≤ (d-1)*(d-2)*(d-3) := by
  classical
  constructor
  · exact bridge_family_external_incidence_budget H S C d hSC hSsize hmax Q W hdis hQ hW hsize hzQ hcross hWmin
  · exact bridge_family_refined_walk_budget H x y hxy S C d L hSC hxC hyC hSsize hmax hSxy Q W hdis hQ hW hsize hxQ hyQ hzQ hcross hWmin hprod
