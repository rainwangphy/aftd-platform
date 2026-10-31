import AFTD.Prelude
import AFTD.Kb.Tcs.AvgPairwiseHammingDist

/-!
# min_avg_pairwise_hamming_dist_density_one_sixteenth_n_eq_five

Topic: combinatorics   Node: 7bf374f2d623

Provenance: helper lemma. arXiv:2610.40486 Sec. 3

For $n = 5$, every subset $F \subseteq (\mathrm{Fin}\ 5 \to \mathrm{Bool})$ of cardinality $2^{5-4} = 2$ has average pairwise Hamming distance at least $(5-4)/2 = 1/2$.
-/

/-- The density 1/16 average Hamming distance lower bound holds for n = 5. -/
theorem min_avg_pairwise_hamming_dist_density_one_sixteenth_n_eq_five
    (F : Finset (Fin 5 → Bool)) (hF : F.card = 2 ^ (5 - 4)) :
    (5 - 4 : ℝ) / 2 ≤ avg_pairwise_hamming_dist F := by
  norm_num at hF ⊢
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hF
  unfold avg_pairwise_hamming_dist
  simp [hab, hammingDist_comm]
  have hd_nat : 1 ≤ hammingDist a b := hammingDist_pos.mpr hab
  have hd : (1 : ℝ) ≤ (hammingDist a b : ℝ) := by exact_mod_cast hd_nat
  have hd' : (1 : ℝ) ≤ (hammingDist b a : ℝ) := by
    simpa [hammingDist_comm] using hd
  norm_num
  linarith
