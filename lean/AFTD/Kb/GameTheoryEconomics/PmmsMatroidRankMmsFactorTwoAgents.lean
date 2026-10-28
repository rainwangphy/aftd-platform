import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMatroidRankValuation
import AFTD.Kb.GameTheoryEconomics.IsPmmsFair
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.PairwiseMaximinShare

/-!
# pmms_matroid_rank_mms_factor_two_agents

Topic: fair_division   Node: c92b02ec1cbe

Provenance: formalization of a published result. Source: arXiv:2012.12710

For two agents with matroid-rank valuations, every complete pairwise maximin-share fair allocation gives each agent at least 1/(2-1) = 1 of her maximin share: MMS_i(2, M) ≤ (2 - 1) * v_i(bundle_of σ i).
-/

lemma pmms_matroid_rank_mms_factor_two_agents_bundle_of_one_eq_sdiff_zero {m : ℕ} (P : Fin m → Fin 2) :
    bundle_of P 1 = Finset.univ \ bundle_of P 0 := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  generalize hy : P x = y
  fin_cases y <;> simp

lemma pmms_matroid_rank_mms_factor_two_agents_bundle_of_union {m : ℕ} (σ : Fin m → Fin 2) (i j : Fin 2) (hij : j ≠ i) :
    bundle_of σ i ∪ bundle_of σ j = Finset.univ := by
  ext x
  simp only [Finset.mem_union, bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases i <;> fin_cases j
  · contradiction
  · generalize hy : σ x = y; fin_cases y <;> simp
  · generalize hy : σ x = y; fin_cases y <;> simp
  · contradiction

lemma pmms_matroid_rank_mms_factor_two_agents_mms_two_le_pairwise (m : ℕ) (u : Finset (Fin m) → ℝ) :
    maximin_share u 2 ≤ pairwise_maximin_share u Finset.univ := by
  dsimp [maximin_share]
  apply ciSup_le
  intro P
  dsimp [pairwise_maximin_share]
  let T : {T : Finset (Fin m) // T ≤ Finset.univ} := ⟨bundle_of P 0, Finset.subset_univ _⟩
  have hbdd_sup : BddAbove (Set.range fun (T : {T : Finset (Fin m) // T ≤ Finset.univ}) =>
      min (u T.1) (u (Finset.univ \ T.1))) := (Set.finite_range _).bddAbove
  have hT : min (u (bundle_of P 0)) (u (Finset.univ \ bundle_of P 0)) ≤
      pairwise_maximin_share u Finset.univ := le_ciSup hbdd_sup T
  have hbdd_inf : BddBelow (Set.range fun k : Fin 2 => u (bundle_of P k)) :=
    (Set.finite_range _).bddBelow
  have h0 : (⨅ k : Fin 2, u (bundle_of P k)) ≤ u (bundle_of P 0) := ciInf_le hbdd_inf 0
  have h1 : (⨅ k : Fin 2, u (bundle_of P k)) ≤ u (bundle_of P 1) := ciInf_le hbdd_inf 1
  have hmin : (⨅ k : Fin 2, u (bundle_of P k)) ≤ min (u (bundle_of P 0)) (u (bundle_of P 1)) :=
    le_min h0 h1
  rw [pmms_matroid_rank_mms_factor_two_agents_bundle_of_one_eq_sdiff_zero P] at hmin
  exact le_trans hmin hT

/-- Case n = 2 of OP-598: PMMS implies MMS for two agents with matroid-rank valuations. -/
theorem pmms_matroid_rank_mms_factor_two_agents (m : ℕ) (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, is_matroid_rank_valuation (v i))
    (σ : Fin m → Fin 2) (hpmms : ∀ i, is_pmms_fair v σ i) (i : Fin 2) :
    maximin_share (v i) 2 ≤ (2 - 1 : ℝ) * v i (bundle_of σ i) := by
  have _ := hv
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have h_union : bundle_of σ i ∪ bundle_of σ j = Finset.univ :=
    pmms_matroid_rank_mms_factor_two_agents_bundle_of_union σ i j hj
  have h_pmms_ij := hpmms i j hj
  rw [h_union] at h_pmms_ij
  have h_mms_le := pmms_matroid_rank_mms_factor_two_agents_mms_two_le_pairwise m (v i)
  have h_le : maximin_share (v i) 2 ≤ v i (bundle_of σ i) := le_trans h_mms_le h_pmms_ij
  have h_factor : (2 - 1 : ℝ) * v i (bundle_of σ i) = v i (bundle_of σ i) := by ring
  rw [h_factor]
  exact h_le
