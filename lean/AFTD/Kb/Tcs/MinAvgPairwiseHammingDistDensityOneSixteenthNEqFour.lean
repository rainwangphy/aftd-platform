import AFTD.Prelude
import AFTD.Kb.Tcs.AvgPairwiseHammingDist
import AFTD.Kb.Tcs.IsSubcube

/-!
# min_avg_pairwise_hamming_dist_density_one_sixteenth_n_eq_four

Topic: combinatorics   Node: 8da667dbd411

Provenance: helper lemma. arXiv:2610.40486 Sec. 3

For $n = 4$, every subset $F \subseteq (\mathrm{Fin}\ 4 \to \mathrm{Bool})$ of cardinality $2^{4-4} = 1$ attains average pairwise Hamming distance $(4-4)/2 = 0$ and is a $0$-dimensional subcube `is_subcube (4 - 4) F`.
-/

/-- The density 1/16 minimum average Hamming distance conjecture holds for n = 4. -/
theorem min_avg_pairwise_hamming_dist_density_one_sixteenth_n_eq_four
    (F : Finset (Fin 4 → Bool)) (hF : F.card = 2 ^ (4 - 4)) :
    avg_pairwise_hamming_dist F = (4 - 4 : ℝ) / 2 ∧ is_subcube (4 - 4) F := by
  obtain ⟨c, hFc⟩ := Finset.card_eq_one.mp (by norm_num at hF; exact hF)
  subst hFc
  constructor
  · unfold avg_pairwise_hamming_dist
    simp [hammingDist_self]
  · refine ⟨Finset.univ, c, ?_, ?_⟩
    · simp
    · ext x
      simp [funext_iff]
