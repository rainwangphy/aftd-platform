import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyVariableExternalIncidenceBudget
import AFTD.Kb.Tcs.BridgeFamilyVariableRefinedWalkBudget

/-!
# bridge_family_variable_shore_incidence_walk_budget

Topic: graphs   Node: 6c403ba4edcf

Provenance: helper lemma. OP-1957 variable-shore refinement of the strict complement walk count.

If every second shore has at least r≥4 vertices, the incidence count and padded-walk gap improve in proportion to r.
-/

theorem bridge_family_variable_shore_incidence_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L r : ℕ) (hr : 4 ≤ r) (hCr : d ≤ C.card) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, r ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card*(Q z).card) :
    let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
    2*C.card ≤ (d-r)*T.card ∧ L*C.card + r*(r-3)*T.card ≤ (d-1)*(d-2)*(d-3) := by
  classical
  constructor
  · exact bridge_family_variable_external_incidence_budget H S C d r hSC hSsize hmax Q W hdis hQ hW hsize hzQ hcross hWmin
  · exact bridge_family_variable_refined_walk_budget H x y hxy S C d L r hr hCr hSC hxC hyC hSsize hmax hSxy Q W hdis hQ hW hsize hxQ hyQ hzQ hcross hWmin hprod
