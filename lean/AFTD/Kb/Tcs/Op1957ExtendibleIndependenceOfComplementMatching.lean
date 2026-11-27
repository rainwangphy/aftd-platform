import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.InducedMatchingLifts
import AFTD.Kb.Tcs.ExtendibleMatchingResidualHasPerfectMatching
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# op1957_extendible_independence_of_complement_matching

Topic: graphs   Node: aa3027faeaf7

Provenance: helper lemma. OP-1957 independence-number reduction

A 4k-vertex k-extendible graph has independence number at most k if the complement of every k+1-vertex set contains a k-matching.
-/

set_option maxHeartbeats 1500000

theorem op1957_extendible_independence_of_complement_matching
    (k : ℕ) (G : SimpleGraph (Fin (4*k)))
    (hext : is_k_extendable G k)
    (hmatcher : ∀ I : Finset (Fin (4*k)), I.card=k+1 →
      ∃ M : (G.induce {v | v ∉ I}).Subgraph, M.IsMatching ∧ M.edgeSet.ncard=k)
    (U : Finset (Fin (4*k)))
    (hind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) : U.card ≤ k := by
  classical
  by_contra hn
  obtain ⟨I,hIU,hI⟩ := Finset.exists_subset_card_eq (s:=U) (n:=k+1) (by omega)
  obtain ⟨M,hM,hMk⟩ := hmatcher I hI
  obtain ⟨N,hN,hNsub,hNk⟩ := induced_matching_lifts G {v | v ∉ I} M hM
  have hNk' : N.edgeSet.ncard=k := by omega
  have hNcard : N.verts.toFinset.card=2*k := by
    rw [←Set.ncard_eq_toFinset_card']
    have hh := in1076_matching_twice_card hN
    omega
  let R := (Finset.univ : Finset (Fin (4*k))) \ N.verts.toFinset
  have hIR : I ⊆ R := by
    intro u hu
    have huN : u ∉ N.verts := fun h => hNsub h hu
    simp [R,huN]
  have hmatch : ∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching := by
    have hRset : {v | v ∈ R} = {v | v ∉ N.verts} := by
      ext v
      simp [R]
    rw [hRset]
    exact extendible_matching_residual_has_perfect_matching G k hext N hN hNk'
  have hcover : ∀ u ∈ I, ∀ v ∈ R, G.Adj u v → v ∈ R \ I := by
    intro u hu v hv hadj
    refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
    intro hvI
    exact hind u (hIU hu) v (hIU hvI) hadj.ne hadj
  have hbound := induced_perfect_matching_neighbors_card_bound G R I (R \ I) hIR hcover hmatch
  have hRcard : R.card=2*k := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hNcard]
    omega
  have hh := Finset.card_sdiff_add_card_inter R I
  rw [Finset.inter_eq_right.mpr hIR,hRcard,hI] at hh
  omega
