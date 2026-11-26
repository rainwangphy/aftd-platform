import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleBalancedCutInternalMatchingComponentBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_balanced_cut_matching_deficiency_two_odd_bound

Topic: graphs   Node: 2cca24d6b6d0

Provenance: helper lemma. Balanced-cut matching obstruction for OP-1957; https://arxiv.org/abs/2611.22690.

Under the stated separator and degree conditions, a balanced side with a matching of k−2 edges has at most two odd components on the opposite side.
-/

theorem extendible_balanced_cut_matching_deficiency_two_odd_bound
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M : G.Subgraph)
    (hM : M.IsMatching) (hMC : M.verts ⊆ (C : Set (Fin (4*k)))) (hm : M.edgeSet.ncard + 2 = k) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  classical
  let R : Set (Fin (4*k)) := {v | v ∉ C}
  let H := G.induce R
  have hsize : Nat.card R = 2*k := by
    rw [Nat.card_coe_set_eq]
    change ((C : Set (Fin (4*k)))ᶜ).ncard = 2*k
    rw [Set.ncard_compl, Set.ncard_coe_finset, Nat.card_eq_fintype_card, Fintype.card_fin, hcard]
    omega
  have hpar := SimpleGraph.odd_ncard_oddComponents H
  rw [hsize, Nat.odd_iff, Nat.odd_iff] at hpar
  by_contra hnot
  change ¬ H.oddComponents.ncard ≤ 2 at hnot
  have hq : 0 < H.oddComponents.ncard := by omega
  obtain ⟨K,hK⟩ := (Set.ncard_pos (Set.toFinite _)).mp hq
  have hlarge : 2 ≤ K.supp.ncard := by
    obtain ⟨a,ha⟩ := K.nonempty_supp
    have hneg : ¬ G.neighborFinset a.val ⊆ C := by
      intro h
      have hh := Finset.card_le_card h
      have hd := hdegree a.val
      omega
    obtain ⟨b,hbN,hbC⟩ := Finset.not_subset.mp hneg
    have hab : G.Adj a.val b := by simpa using hbN
    let b' : R := ⟨b,hbC⟩
    have hb : b' ∈ K.supp := K.mem_supp_of_adj_mem_supp ha hab
    have habne : a ≠ b' := by
      intro h
      have hv := congrArg Subtype.val h
      exact (G.ne_of_adj hab) hv
    have hpair : ({a,b'} : Finset R) ⊆ K.supp.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_toFinset.mpr ha
      · exact Set.mem_toFinset.mpr hb
    have hh := Finset.card_le_card hpair
    rw [Finset.card_pair habne, ← Set.ncard_eq_toFinset_card'] at hh
    exact hh
  have hb := extendible_balanced_cut_internal_matching_component_bound k 2 (by omega)
    G hext hsep C hcard M hM hMC hm K hK hlarge
  change H.oddComponents.ncard ≤ 3 at hb
  omega
