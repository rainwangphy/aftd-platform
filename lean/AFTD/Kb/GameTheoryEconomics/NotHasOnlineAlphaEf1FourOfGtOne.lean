import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm
import AFTD.Kb.GameTheoryEconomics.IsExactPrediction
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.SortedTuple
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1Goods

/-!
# not_has_online_alpha_ef1_four_of_gt_one

Topic: fair_division   Node: 7c33edf6047e

Provenance: helper lemma. step towards op561_tight_ef1_factor_four_agents

For any alpha > 1, there is no deterministic online algorithm guaranteeing an alpha-EF1 allocation for four agents under exact frequency predictions.
-/

/-- No online algorithm can guarantee an alpha-EF1 allocation for four agents when alpha > 1. -/
theorem not_has_online_alpha_ef1_four_of_gt_one {α : ℝ} (hα : 1 < α) :
    ¬ has_online_alpha_ef1_algorithm 4 α := by
  intro h
  simp only [has_online_alpha_ef1_algorithm] at h
  rcases h with ⟨alg, _halg, hgood⟩
  let σ : Fin 5 → Fin 4 := alg 5 (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ))
  have hEF1 : is_alpha_ef1_goods (fun _ _ => (1:ℝ)) α σ :=
    hgood 5 (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) (by intro i g; norm_num) (by intro i; rfl)
  simp only [is_alpha_ef1_goods] at hEF1
  have hsum : ∑ j : Fin 4, (bundle_of σ j).card = 5 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 5)))
      (f := σ) (t := (Finset.univ : Finset (Fin 4))) (by intro x _; exact Finset.mem_univ _)
    simpa [bundle_of, Finset.card_univ, Fintype.card_fin] using h.symm
  have hex_i : ∃ i : Fin 4, (bundle_of σ i).card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have hle : ∑ j : Fin 4, (2:ℕ) ≤ ∑ j : Fin 4, (bundle_of σ j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact hc j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  have hex_j : ∃ j : Fin 4, 2 ≤ (bundle_of σ j).card := by
    by_contra hc
    push_neg at hc
    have hle : ∑ j : Fin 4, (bundle_of σ j).card ≤ ∑ j : Fin 4, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.le_of_lt_succ (hc j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hle
    omega
  obtain ⟨i, hi⟩ := hex_i
  obtain ⟨j, hj⟩ := hex_j
  have hne : i ≠ j := by
    intro heq
    rw [heq] at hi
    omega
  have hnonempty : (bundle_of σ j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g, hg, hineq⟩ := hEF1 i j hne hnonempty
  have hval_erase : additive_valuation (fun x : Fin 5 => (1:ℝ)) ((bundle_of σ j).erase g)
      = (((bundle_of σ j).erase g).card : ℝ) := by
    simp [additive_valuation]
  have hval_i : additive_valuation (fun x : Fin 5 => (1:ℝ)) (bundle_of σ i)
      = ((bundle_of σ i).card : ℝ) := by
    simp [additive_valuation]
  simp only [hval_erase, hval_i] at hineq
  have hcard_erase : (1:ℝ) ≤ (((bundle_of σ j).erase g).card : ℝ) := by
    have h1 : 1 ≤ ((bundle_of σ j).erase g).card := by
      rw [Finset.card_erase_of_mem hg]
      omega
    exact_mod_cast h1
  have hcard_i : ((bundle_of σ i).card : ℝ) ≤ 1 := by
    exact_mod_cast hi
  nlinarith [hineq, hα, hcard_erase, hcard_i]
