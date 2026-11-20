import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeFamilyVariableExternalIncidenceBudget
import AFTD.Kb.Tcs.BridgeFamilyInternalExternalVariableWalkBudget
import AFTD.Kb.Tcs.CompleteBipartiteInternalWalkCharge

/-!
# d11_eighteen_four_shore_has_at_most_four_internal_opposite_vertices

Topic: graphs   Node: 643b402d7b23

Provenance: helper lemma. OP-1957 d=11, k=8 bridge-family analysis; scratch Lean axiom audit completed.

For at least eighteen external endpoints, a four-shore has at most four internal vertices on its opposite side under the displayed product bound.
-/

theorem d11_eighteen_four_shore_has_at_most_four_internal_opposite_vertices
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C : Finset V) (hC : 18 ≤ C.card) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card+1=11)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hsize : ∀ z ∈ C, (Q z).card + (W z).card = 12)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card)
    (hprod : ∀ z ∈ C, 32 ≤ (W z).card*(Q z).card) :
    ∀ z ∈ C, (W z).card = 4 → (Q z ∩ S).card ≤ 4 := by
  classical
  intro z hz hwcard
  have hinc := bridge_family_variable_external_incidence_budget H S C 11 4 hSC hS hmax Q W hdis hQ hW
    (by intro a ha; simpa using hsize a ha) hzQ hcross hWmin
  have hwalk := bridge_family_internal_external_variable_walk_budget H x y hxy S C 11 32 4
    (by omega) (by omega) hSC hxC hyC hS hmax hSxy Q W hdis hQ hW
    (by intro a ha; simpa using hsize a ha) hxQ hyQ hzQ hcross hWmin hprod
  have hdis' : Disjoint (W z) (Q z ∩ S) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp (hdis z hz)) (Finset.mem_inter.mp hb).1 ha
  have hcharge := complete_bipartite_internal_walk_charge H S (W z) (Q z ∩ S)
    (hW z hz) Finset.inter_subset_right hdis' hwcard
    (by intro a ha b hb; exact (hcross z hz b (Finset.mem_inter.mp hb).1 a ha).symm)
  simp only [Nat.reduceSub, Nat.reduceMul] at hinc hwalk
  have hT : 6 ≤ (C.filter (fun q => 4 ≤ (H.neighborFinset q ∩ S).card)).card := by omega
  by_contra hp
  have hp3 : 5 ≤ (Q z ∩ S).card := by omega
  have hp2 : 4 ≤ (Q z ∩ S).card-1 := by omega
  have hprod' := Nat.mul_le_mul hp3 hp2
  simp only [Nat.mul_assoc] at hcharge
  omega
