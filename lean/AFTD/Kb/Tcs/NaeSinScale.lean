import AFTD.Prelude

/-!
# nae_sin_scale

Topic: quantum   Node: b074eda2b931

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For 0 ≤ t ≤ π, sin(15t/16) is at least (15/16) sin t.
-/

theorem nae_sin_scale (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ Real.pi) :
    (15 / 16 : ℝ) * Real.sin t ≤ Real.sin ((15 / 16 : ℝ) * t) := by
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show t ∈ Set.Icc 0 Real.pi from ⟨ht0, htpi⟩)
    (show 0 ≤ 1 - (15 / 16 : ℝ) by norm_num)
    (show 0 ≤ (15 / 16 : ℝ) by norm_num)
    (show 1 - (15 / 16 : ℝ) + 15 / 16 = 1 by norm_num)
  simpa [smul_eq_mul] using h
