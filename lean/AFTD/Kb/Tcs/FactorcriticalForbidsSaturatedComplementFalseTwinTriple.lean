import AFTD.Prelude
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_forbids_saturated_complement_false_twin_triple

Topic: graphs   Node: 549a325197eb

Provenance: helper lemma. OP-1957 codegree-three Tutte case: a saturated false-twin triple and its common neighborhood form an odd anticomplete residual.

A 2k-factor-critical complement graph of order 2k+d+3 has no three vertices with the same d-element complement neighborhood.
-/

theorem factorcritical_forbids_saturated_complement_false_twin_triple (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical Hᶜ (2*k)) (T : Finset (Fin (2*k+d+3)))
    (hT : T.card = 3) (hdeg : ∀ a ∈ T, (H.neighborFinset a).card = d)
    (htwin : ∀ a ∈ T, ∀ b ∈ T, H.neighborFinset a = H.neighborFinset b) : False := by
  classical
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := hTne
  let N := H.neighborFinset a
  have hdisj : Disjoint T N := by
    apply Finset.disjoint_left.mpr
    intro b hb hbn
    have hbn' : b ∈ H.neighborFinset b := by
      rw [htwin b hb a ha]
      exact hbn
    exact H.irrefl ((H.mem_neighborFinset b b).mp hbn')
  have hcross : ∀ b ∈ T, ∀ c ∈ N, ¬ Hᶜ.Adj b c := by
    intro b hb c hc h
    have hbc : H.Adj b c := by
      apply (H.mem_neighborFinset b c).mp
      rw [htwin b hb a ha]
      exact hc
    exact h.2 hbc
  have hN : N.card = d := hdeg a ha
  have hunion : (T ∪ N).card = d+3 := by
    rw [Finset.card_union_of_disjoint hdisj, hT, hN]
    omega
  have hcut : ((Finset.univ : Finset (Fin (2*k+d+3))) \ (T ∪ N)).card = 2*k := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (T ∪ N))
    simp only [Finset.card_univ, Fintype.card_fin, hunion] at h
    omega
  have he := factor_critical_anticomplete_cut_side_even Hᶜ (2*k) hcrit T N hdisj hcross hcut
  rw [hT] at he
  norm_num at he
