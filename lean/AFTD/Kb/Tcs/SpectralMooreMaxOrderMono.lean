import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreMaxOrder
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe

/-!
# spectral_moore_max_order_mono

Topic: graphs   Node: 2eeb66569fa3

Provenance: helper lemma. Sanity lemma for spectral_moore_max_order (arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), noted after Theorem 2.3: v(k, θ) ≤ v(k, ⌈θ⌉)).

Sanity lemma: v(k, θ) is monotone in θ.
-/

theorem spectral_moore_max_order_mono (k : ℕ) {θ θ' : ℝ} (h : θ ≤ θ') :
    spectral_moore_max_order k θ ≤ spectral_moore_max_order k θ' := by
  classical
  unfold spectral_moore_max_order
  refine iSup₂_le fun n G => iSup_le fun hG => ?_
  refine le_iSup₂_of_le n G (le_iSup_of_le ⟨hG.1, ?_, ?_⟩ le_rfl)
  · convert hG.2.1
  · intro i hi
    exact (hG.2.2 i hi).trans h
