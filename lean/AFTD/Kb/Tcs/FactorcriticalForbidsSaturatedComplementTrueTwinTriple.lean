import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound

/-!
# factorcritical_forbids_saturated_complement_true_twin_triple

Topic: graphs   Node: 7c9ddd68278d

Provenance: helper lemma. OP-1957 codegree-three Tutte case: three saturated true complement twins would have only two available matching partners in a suitable residual.

A 2k-factor-critical complement graph of order 2k+d+3 has no three vertices with the same (d+1)-element closed complement neighborhood and complement degree d.
-/

theorem factorcritical_forbids_saturated_complement_true_twin_triple (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (T : Finset (Fin (2*k+d+3)))
    (hT : T.card = 3) (hdeg : ∀ a ∈ T, (H.neighborFinset a).card = d)
    (htwin : ∀ a ∈ T, ∀ b ∈ T, insert a (H.neighborFinset a) = insert b (H.neighborFinset b)) : False := by
  classical
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := hTne
  let N := insert a (H.neighborFinset a)
  have hanot : a ∉ H.neighborFinset a := by simp [SimpleGraph.mem_neighborFinset]
  have hNcard : N.card = d+1 := by
    dsimp [N]
    rw [Finset.card_insert_of_notMem hanot, hdeg a ha]
  have hTN : T ⊆ N := by
    intro t ht
    have h : t ∈ insert t (H.neighborFinset t) := Finset.mem_insert_self _ _
    rw [htwin t ht a ha] at h
    exact h
  let C := (Finset.univ : Finset (Fin (2*k+d+3))) \ N
  have hCcard : C.card = 2*k+2 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    simp only [Finset.card_univ, Fintype.card_fin, hNcard] at h
    dsimp [C]
    omega
  have hCtwo : 2 ≤ C.card := by omega
  obtain ⟨P,hPC,hPcard⟩ := Finset.exists_subset_card_eq hCtwo
  let R := N ∪ P
  have hNP : Disjoint N P := by
    apply Finset.disjoint_left.mpr
    intro b hbN hbP
    have hbC := hPC hbP
    exact (Finset.mem_sdiff.mp hbC).2 hbN
  have hRcard : R.card = d+3 := by
    dsimp [R]
    rw [Finset.card_union_of_disjoint hNP, hNcard, hPcard]
  have hcut : ((Finset.univ : Finset (Fin (2*k+d+3))) \ R).card = 2*k := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
    simp only [Finset.card_univ, Fintype.card_fin, hRcard] at h
    omega
  let D := (Finset.univ : Finset (Fin (2*k+d+3))) \ R
  have hmatch : ∃ M : ((Hᶜ).induce {v | v ∈ R}).Subgraph, M.IsPerfectMatching := by
    have h := hcrit D hcut
    have heq : (D : Set (Fin (2*k+d+3)))ᶜ = {v | v ∈ R} := by
      ext v
      simp [D]
    rw [heq] at h
    exact h
  have hTR : T ⊆ R := fun t ht => Finset.mem_union_left P (hTN ht)
  have hcover : ∀ t ∈ T, ∀ v ∈ R, Hᶜ.Adj t v → v ∈ P := by
    intro t ht v hv hadj
    rcases Finset.mem_union.mp hv with hvN | hvP
    · have htN : N = insert t (H.neighborFinset t) := (htwin t ht a ha).symm
      rw [htN] at hvN
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hvN
      rcases hvN with h | h
      · exact (hadj.1 h.symm).elim
      · exact (hadj.2 h).elim
    · exact hvP
  have hc := induced_perfect_matching_neighbors_card_bound Hᶜ R T P hTR hcover hmatch
  rw [hT,hPcard] at hc
  omega
