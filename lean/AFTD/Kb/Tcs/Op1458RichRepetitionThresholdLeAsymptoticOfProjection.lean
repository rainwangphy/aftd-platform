import AFTD.Prelude
import AFTD.Kb.Tcs.UWord
import AFTD.Kb.Tcs.WordAsymptoticCriticalExponent
import AFTD.Kb.Tcs.WordCriticalExponent
import AFTD.Kb.Tcs.RichRepetitionThreshold
import AFTD.Kb.Tcs.IsMorphicImage
import AFTD.Kb.Tcs.IsRichWord
import AFTD.Kb.Tcs.IsUniformlyRecurrentWord
import AFTD.Kb.Tcs.RichWordCriticalExponents

/-!
# op_1458_rich_repetition_threshold_le_asymptotic_of_projection

Topic: combinatorics   Node: e68835fe49e8

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 8, item 1

For any integer d ≥ 2, if there exist a morphism π : Fin (2 * d - 1) → List (Fin d) and an infinite word z : ℕ → Fin d such that z is the morphic image of u_{2d-1} under π, z is uniformly recurrent and rich in palindromes, and the critical exponent of z equals the asymptotic critical exponent of u_{2d-1}, then the repetition threshold RT(C_d) is at most the asymptotic critical exponent of u_{2d-1}.
-/

/-- The upper bound RT(C_d) ≤ E*(u_{2d-1}) follows from the existence of a uniformly recurrent rich projection. -/
theorem op_1458_rich_repetition_threshold_le_asymptotic_of_projection
    (d : ℕ) (hd : 2 ≤ d)
    (π : Fin (2 * d - 1) → List (Fin d)) (z : ℕ → Fin d)
    (hz_morph : is_morphic_image z π (u_word (2 * d - 1) (by omega)))
    (hz_rec : is_uniformly_recurrent_word z)
    (hz_rich : is_rich_word z)
    (hz_crit : word_critical_exponent z = word_asymptotic_critical_exponent (u_word (2 * d - 1) (by omega))) :
    rich_repetition_threshold d ≤ word_asymptotic_critical_exponent (u_word (2 * d - 1) (by omega)) := by
  have hbdd : BddBelow (rich_word_critical_exponents d) := by
    refine ⟨0, ?_⟩
    rintro e ⟨w, -, -, rfl⟩
    exact Real.sSup_nonneg (by
      rintro q ⟨x, y, m, hx, -, -, rfl⟩
      have hxpos : (0 : ℝ) < (x.length : ℝ) := by
        have : 0 < x.length := List.length_pos_iff.mpr hx
        exact_mod_cast this
      positivity)
  have hmem : word_critical_exponent z ∈ rich_word_critical_exponents d :=
    ⟨z, hz_rec, hz_rich, rfl⟩
  rw [← hz_crit]
  exact csInf_le hbdd hmem
