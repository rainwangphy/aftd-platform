import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.BalancedCutEvenlyDistributedCrossMatching
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutOddBoundOfParityCrossMatching

/-!
# extendible_balanced_cut_matching_deficiency_odd_bound

Topic: graphs   Node: 526e1bd2551b

Provenance: helper lemma. Balanced-cut structural reduction for OP-1957; https://arxiv.org/abs/2611.22690.

In an order-4k k-extendible graph with the stated 2k-separator and degree bounds, a balanced side containing a matching with deficit r has at most r+1 odd components on the other side.
-/

theorem extendible_balanced_cut_matching_deficiency_odd_bound
    (k r : ℕ) (hr : 1 ≤ r)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph)
    (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hm : M.edgeSet.ncard + r = k) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r+1 := by
  set_option maxHeartbeats 4000000 in
    classical
    by_contra hnot
    let R : Set (Fin (4*k)) := {v | v ∉ C}
    let H := G.induce R
    let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let F : H.ConnectedComponent → Finset (Fin (4*k)) := in1206_component_vertices G R
    have hO : r+2 ≤ O.card := by
      have heq : O.card = H.oddComponents.ncard := by
        dsimp [O]
        exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
      change ¬ H.oddComponents.ncard ≤ r+1 at hnot
      omega
    have hCH : ∀ i ∈ O, Disjoint C (F i) := by
      intro i hi
      apply Finset.disjoint_left.mpr
      intro v hvC hvF
      have hvR : v ∈ R := (induced_component_ambient_vertex_properties G R i i).1 hvF
      exact hvR hvC
    have hdis : ∀ i ∈ O, ∀ j ∈ O, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact (induced_component_ambient_vertex_properties G R i j).2.2.1 hij
    have hsize : ∀ i ∈ O, 2 ≤ (F i).card := by
      intro i hi
      have hc := (induced_component_ambient_vertex_properties G R i i).2.1
      change 2 ≤ (in1206_component_vertices G R i).card
      rw [hc]
      obtain ⟨a,ha⟩ := i.nonempty_supp
      have hneg : ¬ G.neighborFinset a.val ⊆ C := by
        intro h
        have hh := Finset.card_le_card h
        have hd := hdegree a.val
        omega
      obtain ⟨b,hbN,hbC⟩ := Finset.not_subset.mp hneg
      have hab : G.Adj a.val b := by simpa using hbN
      let b' : R := ⟨b,hbC⟩
      have hb : b' ∈ i.supp := i.mem_supp_of_adj_mem_supp ha hab
      have habne : a ≠ b' := by
        intro he
        have hv := congrArg Subtype.val he
        exact (G.ne_of_adj hab) hv
      have hpair : ({a,b'} : Finset R) ⊆ i.supp.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Set.mem_toFinset.mpr ha
        · exact Set.mem_toFinset.mpr hb
      have hh := Finset.card_le_card hpair
      rw [Finset.card_pair habne, ← Set.ncard_eq_toFinset_card'] at hh
      exact hh
    have hanti : ∀ i ∈ O, ∀ u ∈ F i, ∀ v, v ∉ C → v ∉ F i → ¬ G.Adj u v := by
      intro i hi u hu v hvC hvF
      exact (induced_component_ambient_vertex_properties G R i i).2.2.2 u hu v hvC hvF
    have hcross : ∀ U : Finset (Fin (4*k)), U ⊆ C → U.card = 2*r →
        ∃ f g : Fin r → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
          (∀ i, f i ∈ U ∧ g i ∉ C ∧ G.Adj (f i) (g i)) ∧
          ∃ B : Finset H.ConnectedComponent, B.card ≤ 1 ∧
            ∀ i ∈ H.oddComponents.toFinset, i ∉ B →
              Even ((F i) ∩ ((Finset.univ : Finset (Fin r)).image g)).card := by
      intro U hUC hU
      obtain ⟨f,g,hf,hg,hfg,hgroups,B,hB,hpar⟩ :=
        balanced_cut_evenly_distributed_cross_matching k r G hsep C U hcard hUC (by omega) O F hO hCH hdis hsize hanti
      refine ⟨f,g,hf,hg,?_,B,hB,?_⟩
      · intro a
        obtain ⟨i,hi,hgi⟩ := hgroups a
        refine ⟨(hfg a).1,?_,(hfg a).2⟩
        intro hgC
        exact Finset.disjoint_left.mp (hCH i hi) hgC hgi
      · intro i hi hiB
        have hh := hpar i hi hiB
        simpa [Finset.inter_comm] using hh
    have hb := extendible_balanced_cut_odd_bound_of_parity_cross_matching k r G hext C hcard M hM hMC hm hcross
    exact hnot hb
