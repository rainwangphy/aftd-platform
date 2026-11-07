import AFTD.Prelude
import AFTD.Kb.Tcs.FourierCrossLevel
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# fourier_cross_level_eq_zero_of_card_lt

Topic: combinatorics   Node: d2569943c3b5

Provenance: helper lemma. arXiv:2611.08289 Section 2.1

For any two functions $f, g : \{0,1\}^n \to \mathbb{R}$ and any integer $k > n$, the $k$-th cross Fourier level $W_k[f,g]$ equals zero.
-/

/-- The cross Fourier level W_k[f,g] vanishes when k > n. -/
theorem fourier_cross_level_eq_zero_of_card_lt {n k : ℕ} (h : n < k) (f g : BooleanAnalysis.BooleanFunc n) :
    fourier_cross_level k f g = 0 := by
  unfold fourier_cross_level
  have h_card : Finset.card (Finset.univ : Finset (Fin n)) = n := Finset.card_fin n
  have h_empty : Finset.powersetCard k (Finset.univ : Finset (Fin n)) = ∅ := by
    rw [Finset.powersetCard_eq_empty, h_card]
    exact h
  rw [h_empty, Finset.sum_empty]
