import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.PerfectMatchingOddAnticompleteGroupsBound
import AFTD.Kb.Tcs.BalancedCutAnticompleteSideHasCrossMatching
import AFTD.Kb.Tcs.ExtendibleMatchingResidualHasPerfectMatching
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.BalancedCutExtendInternalMatching
import AFTD.Kb.Tcs.OddComponentBoundAfterForcedMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# extendible_balanced_cut_internal_matching_component_bound

Topic: graphs   Node: a6a317d7c11c

Provenance: helper lemma. Balanced-cut matching obstruction for OP-1957; https://arxiv.org/abs/2611.22690.

In an order-4k extendible graph with the displayed 2k-separator property, a balanced side containing a matching of k−r edges forces at most r+1 odd components on the other side if one of them contains at least r vertices.
-/

theorem extendible_balanced_cut_internal_matching_component_bound
    (k r : ℕ) (hr : 1 ≤ r)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph)
    (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k)))) (hm : M.edgeSet.ncard + r = k)
    (K : (G.induce {v | v ∉ C}).ConnectedComponent)
    (hK : K ∈ (G.induce {v | v ∉ C}).oddComponents)
    (hlarge : r ≤ K.supp.ncard) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r+1 := by
  classical
  let R : Set (Fin (4*k)) := {v | v ∉ C}
  let H := in1206_component_vertices G R K
  have hprops := induced_component_ambient_vertex_properties G R K K
  have hCH : Disjoint C H := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvH
    have hvR : v ∈ R := hprops.1 hvH
    exact hvR hvC
  have hanti : ∀ u ∈ H, ∀ v, v ∉ C → v ∉ H → ¬ G.Adj u v := by
    intro u hu v hvC hvH
    exact hprops.2.2.2 u hu v hvC hvH
  have hrH : r ≤ H.card := by
    rw [hprops.2.1]
    exact hlarge
  obtain ⟨T,hT,hTcard,hMT,hsub,hremain⟩ :=
    balanced_cut_extend_internal_matching k r hr G hsep C H hcard hCH
      hanti hrH M hM hMC hm
  obtain ⟨P,hP,hTP⟩ := hext.2.2 T hT hTcard
  apply odd_component_bound_after_forced_matching k r G C K hK P T hP hT hTP
  · simpa [H,R] using hsub
  · exact hremain
