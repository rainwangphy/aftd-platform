import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.BalancedCutEvenlyDistributedCrossMatchingSharp
import AFTD.Kb.Tcs.BalancedCutEvenComponentParityCrossMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutOddBoundOfEvenCrossMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# extendible_balanced_cut_even_component_odd_bound

Topic: graphs   Node: 7df311537143

Provenance: helper lemma. Balanced-cut parity reduction for OP-1957; https://arxiv.org/abs/2611.22690.

Under the displayed extendibility, separator, degree, and balanced-side matching conditions, if the opposite side has an even component then it has at most r odd components.
-/

theorem extendible_balanced_cut_even_component_odd_bound
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph) (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hm : M.edgeSet.ncard+r=k)
    (K : (G.induce {v | v ∉ C}).ConnectedComponent)
    (hK : K ∉ (G.induce {v | v ∉ C}).oddComponents) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r := by
  set_option maxHeartbeats 4000000 in
    classical
    by_contra hnot
    let R : Set (Fin (4*k)) := {v | v ∉ C}
    let H := G.induce R
    let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let F : H.ConnectedComponent → Finset (Fin (4*k)) := in1206_component_vertices G R
    have hRsize : Nat.card R = 2*k := by
      rw [Nat.card_coe_set_eq]
      change ((C : Set (Fin (4*k)))ᶜ).ncard = 2*k
      rw [Set.ncard_compl, Set.ncard_coe_finset, Nat.card_eq_fintype_card, Fintype.card_fin, hcard]
      omega
    have hpar := SimpleGraph.odd_ncard_oddComponents H
    rw [hRsize,Nat.odd_iff,Nat.odd_iff] at hpar
    have hOcard : O.card = H.oddComponents.ncard := by
      dsimp [O]
      exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
    have hq : r+1 ≤ O.card := by
      change ¬ H.oddComponents.ncard ≤ r at hnot
      omega
    have hCH : ∀ i ∈ O, Disjoint C (F i) := by
      intro i hi
      apply Finset.disjoint_left.mpr
      intro v hvC hvF
      have hvR : v ∈ R := (induced_component_ambient_vertex_properties G R i i).1 hvF
      exact hvR hvC
    have hCK : Disjoint C (F K) := by
      apply Finset.disjoint_left.mpr
      intro v hvC hvF
      have hvR : v ∈ R := (induced_component_ambient_vertex_properties G R K K).1 hvF
      exact hvR hvC
    have hdis : ∀ i ∈ O, ∀ j ∈ O, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact (induced_component_ambient_vertex_properties G R i j).2.2.1 hij
    have hKF : ∀ i ∈ O, Disjoint (F K) (F i) := by
      intro i hi
      have hi' : i ∈ H.oddComponents := by simpa [O] using hi
      have hne : K ≠ i := by
        intro he
        apply hK
        simpa [R,H,he] using hi'
      exact (induced_component_ambient_vertex_properties G R K i).2.2.1 hne
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
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Set.mem_toFinset.mpr ha
        · exact Set.mem_toFinset.mpr hb
      have hh := Finset.card_le_card hpair
      rw [Finset.card_pair habne, ← Set.ncard_eq_toFinset_card'] at hh
      exact hh
    have hKN : (F K).Nonempty := by
      obtain ⟨a,ha⟩ := K.nonempty_supp
      have hn : 0 < K.supp.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨a,ha⟩
      apply Finset.card_pos.mp
      have hc := (induced_component_ambient_vertex_properties G R K K).2.1
      change 0 < (in1206_component_vertices G R K).card
      omega
    have hanti : ∀ i ∈ O, ∀ u ∈ F i, ∀ v, v ∉ C → v ∉ F i → ¬ G.Adj u v := by
      intro i hi u hu v hvC hvF
      exact (induced_component_ambient_vertex_properties G R i i).2.2.2 u hu v hvC hvF
    have hKanti : ∀ u ∈ F K, ∀ v, v ∉ C → v ∉ F K → ¬ G.Adj u v := by
      intro u hu v hvC hvF
      exact (induced_component_ambient_vertex_properties G R K K).2.2.2 u hu v hvC hvF
    have hcross : ∀ U : Finset (Fin (4*k)), U ⊆ C → U.card = 2*r →
        ∃ f g : Fin r → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
          (∀ i, f i ∈ U ∧ g i ∉ C ∧ G.Adj (f i) (g i)) ∧
          ∃ B : Finset H.ConnectedComponent, B.card = 0 ∧
            ∀ i ∈ H.oddComponents.toFinset, i ∉ B →
              Even ((F i) ∩ ((Finset.univ : Finset (Fin r)).image g)).card := by
      intro U hUC hU
      by_cases hre : Even r
      · have hrmod : r%2 = 0 := Nat.even_iff.mp hre
        have hO : r+2 ≤ O.card := by omega
        obtain ⟨f,g,hf,hg,hfg,hgroups,B,hB,hp⟩ :=
          balanced_cut_evenly_distributed_cross_matching_sharp k r G hsep C U hcard hUC (by omega) O F hO hCH hdis hsize hanti
        refine ⟨f,g,hf,hg,?_,B,by omega,?_⟩
        · intro a
          obtain ⟨i,hi,hgi⟩ := hgroups a
          refine ⟨(hfg a).1,?_,(hfg a).2⟩
          intro hgC
          exact Finset.disjoint_left.mp (hCH i hi) hgC hgi
        · intro i hi hiB
          simpa [Finset.inter_comm] using hp i hi hiB
      · cases r with
        | zero => exact False.elim (hre (by simp))
        | succ n =>
          have hn : Even n := by
            rw [Nat.even_iff] at hre ⊢
            omega
          have hO : n+2 ≤ O.card := by omega
          obtain ⟨f,g,hf,hg,hfg,hp⟩ :=
            balanced_cut_even_component_parity_cross_matching k n hn G hsep C U (F K) hcard hUC (by omega)
              hCK hKN hKanti O F hO hCH hKF hdis hsize hanti
          refine ⟨f,g,hf,hg,hfg,∅,by simp,?_⟩
          intro i hi _
          simpa [Finset.inter_comm] using hp i hi
    have hb := extendible_balanced_cut_odd_bound_of_even_cross_matching k r G hext C hcard M hM hMC hm hcross
    exact hnot hb
