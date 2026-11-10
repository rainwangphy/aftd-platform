import AFTD.Prelude

/-!
# strong_euclidean_extension_exponent_gap_nonnegative

Topic: algorithms   Node: 59b9e2b4e351

Provenance: helper lemma. arXiv:2611.08546, equation (18), with the weaker exponent η = 179/200 used by one_strongly_euclidean_union_sublinear_distortion.

The quartic exponent condition in arXiv:2611.08546, equation (18), holds for η = 179/200 throughout the unit interval.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

noncomputable def in697_gap (z : ℝ) : ℝ :=
  (1 + (179 / 200 : ℝ))^2 * (1-z^2)^2 + (1 + (179 / 400 : ℝ))^2 * z^2 * (2-z^2) - (1/2 : ℝ) * (z+1)^2 * (2-z^2)

lemma in697_gap_interval_0 (z : ℝ) (hl : 0 ≤ z) (hr : z ≤ (1/2 : ℝ)) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - 0 := by linarith
  have hq : 0 ≤ (1/2 : ℝ) - z := by linarith
  have hcert : 0 ≤ (103641/2500 : ℝ) * (z - 0)^0 * ((1/2 : ℝ) - z)^4 +
      (93641/625 : ℝ) * (z - 0)^1 * ((1/2 : ℝ) - z)^3 +
      (747089/4000 : ℝ) * (z - 0)^2 * ((1/2 : ℝ) - z)^2 +
      (918933/10000 : ℝ) * (z - 0)^3 * ((1/2 : ℝ) - z)^1 +
      (2477763/160000 : ℝ) * (z - 0)^4 * ((1/2 : ℝ) - z)^0 := by positivity
  have hid : in697_gap z = (103641/2500 : ℝ) * (z - 0)^0 * ((1/2 : ℝ) - z)^4 +
      (93641/625 : ℝ) * (z - 0)^1 * ((1/2 : ℝ) - z)^3 +
      (747089/4000 : ℝ) * (z - 0)^2 * ((1/2 : ℝ) - z)^2 +
      (918933/10000 : ℝ) * (z - 0)^3 * ((1/2 : ℝ) - z)^1 +
      (2477763/160000 : ℝ) * (z - 0)^4 * ((1/2 : ℝ) - z)^0 := by unfold in697_gap; ring
  linarith

lemma in697_gap_interval_1 (z : ℝ) (hl : (1/2 : ℝ) ≤ z) (hr : z ≤ (3/4 : ℝ)) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - (1/2 : ℝ) := by linarith
  have hq : 0 ≤ (3/4 : ℝ) - z := by linarith
  have hcert : 0 ≤ (2477763/10000 : ℝ) * (z - (1/2 : ℝ))^0 * ((3/4 : ℝ) - z)^4 +
      (3757557/5000 : ℝ) * (z - (1/2 : ℝ))^1 * ((3/4 : ℝ) - z)^3 +
      (3135641/4000 : ℝ) * (z - (1/2 : ℝ))^2 * ((3/4 : ℝ) - z)^2 +
      (6487153/20000 : ℝ) * (z - (1/2 : ℝ))^3 * ((3/4 : ℝ) - z)^1 +
      (7388523/160000 : ℝ) * (z - (1/2 : ℝ))^4 * ((3/4 : ℝ) - z)^0 := by positivity
  have hid : in697_gap z = (2477763/10000 : ℝ) * (z - (1/2 : ℝ))^0 * ((3/4 : ℝ) - z)^4 +
      (3757557/5000 : ℝ) * (z - (1/2 : ℝ))^1 * ((3/4 : ℝ) - z)^3 +
      (3135641/4000 : ℝ) * (z - (1/2 : ℝ))^2 * ((3/4 : ℝ) - z)^2 +
      (6487153/20000 : ℝ) * (z - (1/2 : ℝ))^3 * ((3/4 : ℝ) - z)^1 +
      (7388523/160000 : ℝ) * (z - (1/2 : ℝ))^4 * ((3/4 : ℝ) - z)^0 := by unfold in697_gap; ring
  linarith

lemma in697_gap_interval_2 (z : ℝ) (hl : (3/4 : ℝ) ≤ z) (hr : z ≤ (7/8 : ℝ)) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - (3/4 : ℝ) := by linarith
  have hq : 0 ≤ (7/8 : ℝ) - z := by linarith
  have hcert : 0 ≤ (7388523/10000 : ℝ) * (z - (3/4 : ℝ))^0 * ((7/8 : ℝ) - z)^4 +
      (9191263/5000 : ℝ) * (z - (3/4 : ℝ))^1 * ((7/8 : ℝ) - z)^3 +
      (28665433/20000 : ℝ) * (z - (3/4 : ℝ))^2 * ((7/8 : ℝ) - z)^2 +
      (7261863/20000 : ℝ) * (z - (3/4 : ℝ))^3 * ((7/8 : ℝ) - z)^1 +
      (4994811/160000 : ℝ) * (z - (3/4 : ℝ))^4 * ((7/8 : ℝ) - z)^0 := by positivity
  have hid : in697_gap z = (7388523/10000 : ℝ) * (z - (3/4 : ℝ))^0 * ((7/8 : ℝ) - z)^4 +
      (9191263/5000 : ℝ) * (z - (3/4 : ℝ))^1 * ((7/8 : ℝ) - z)^3 +
      (28665433/20000 : ℝ) * (z - (3/4 : ℝ))^2 * ((7/8 : ℝ) - z)^2 +
      (7261863/20000 : ℝ) * (z - (3/4 : ℝ))^3 * ((7/8 : ℝ) - z)^1 +
      (4994811/160000 : ℝ) * (z - (3/4 : ℝ))^4 * ((7/8 : ℝ) - z)^0 := by unfold in697_gap; ring
  linarith

lemma in697_gap_interval_3 (z : ℝ) (hl : (7/8 : ℝ) ≤ z) (hr : z ≤ (29/32 : ℝ)) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - (7/8 : ℝ) := by linarith
  have hq : 0 ≤ (29/32 : ℝ) - z := by linarith
  have hcert : 0 ≤ (4994811/625 : ℝ) * (z - (7/8 : ℝ))^0 * ((29/32 : ℝ) - z)^4 +
      (10450329/625 : ℝ) * (z - (7/8 : ℝ))^1 * ((29/32 : ℝ) - z)^3 +
      (53560777/5000 : ℝ) * (z - (7/8 : ℝ))^2 * ((29/32 : ℝ) - z)^2 +
      (34850481/10000 : ℝ) * (z - (7/8 : ℝ))^3 * ((29/32 : ℝ) - z)^1 +
      (240594763/160000 : ℝ) * (z - (7/8 : ℝ))^4 * ((29/32 : ℝ) - z)^0 := by positivity
  have hid : in697_gap z = (4994811/625 : ℝ) * (z - (7/8 : ℝ))^0 * ((29/32 : ℝ) - z)^4 +
      (10450329/625 : ℝ) * (z - (7/8 : ℝ))^1 * ((29/32 : ℝ) - z)^3 +
      (53560777/5000 : ℝ) * (z - (7/8 : ℝ))^2 * ((29/32 : ℝ) - z)^2 +
      (34850481/10000 : ℝ) * (z - (7/8 : ℝ))^3 * ((29/32 : ℝ) - z)^1 +
      (240594763/160000 : ℝ) * (z - (7/8 : ℝ))^4 * ((29/32 : ℝ) - z)^0 := by unfold in697_gap; ring
  linarith

lemma in697_gap_interval_4 (z : ℝ) (hl : (29/32 : ℝ) ≤ z) (hr : z ≤ (15/16 : ℝ)) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - (29/32 : ℝ) := by linarith
  have hq : 0 ≤ (15/16 : ℝ) - z := by linarith
  have hcert : 0 ≤ (240594763/160000 : ℝ) * (z - (29/32 : ℝ))^0 * ((15/16 : ℝ) - z)^4 +
      (170893801/20000 : ℝ) * (z - (29/32 : ℝ))^1 * ((15/16 : ℝ) - z)^3 +
      (4142573/160 : ℝ) * (z - (29/32 : ℝ))^2 * ((15/16 : ℝ) - z)^2 +
      (162132353/5000 : ℝ) * (z - (29/32 : ℝ))^3 * ((15/16 : ℝ) - z)^1 +
      (135783579/10000 : ℝ) * (z - (29/32 : ℝ))^4 * ((15/16 : ℝ) - z)^0 := by positivity
  have hid : in697_gap z = (240594763/160000 : ℝ) * (z - (29/32 : ℝ))^0 * ((15/16 : ℝ) - z)^4 +
      (170893801/20000 : ℝ) * (z - (29/32 : ℝ))^1 * ((15/16 : ℝ) - z)^3 +
      (4142573/160 : ℝ) * (z - (29/32 : ℝ))^2 * ((15/16 : ℝ) - z)^2 +
      (162132353/5000 : ℝ) * (z - (29/32 : ℝ))^3 * ((15/16 : ℝ) - z)^1 +
      (135783579/10000 : ℝ) * (z - (29/32 : ℝ))^4 * ((15/16 : ℝ) - z)^0 := by unfold in697_gap; ring
  linarith

lemma in697_gap_interval_5 (z : ℝ) (hl : (15/16 : ℝ) ≤ z) (hr : z ≤ 1) : 0 ≤ in697_gap z := by
  have hp : 0 ≤ z - (15/16 : ℝ) := by linarith
  have hq : 0 ≤ 1 - z := by linarith
  have hcert : 0 ≤ (135783579/160000 : ℝ) * (z - (15/16 : ℝ))^0 * (1 - z)^4 +
      (15326149/2500 : ℝ) * (z - (15/16 : ℝ))^1 * (1 - z)^3 +
      (9887468/625 : ℝ) * (z - (15/16 : ℝ))^2 * (1 - z)^2 +
      (10486784/625 : ℝ) * (z - (15/16 : ℝ))^3 * (1 - z)^1 +
      (3901696/625 : ℝ) * (z - (15/16 : ℝ))^4 * (1 - z)^0 := by positivity
  have hid : in697_gap z = (135783579/160000 : ℝ) * (z - (15/16 : ℝ))^0 * (1 - z)^4 +
      (15326149/2500 : ℝ) * (z - (15/16 : ℝ))^1 * (1 - z)^3 +
      (9887468/625 : ℝ) * (z - (15/16 : ℝ))^2 * (1 - z)^2 +
      (10486784/625 : ℝ) * (z - (15/16 : ℝ))^3 * (1 - z)^1 +
      (3901696/625 : ℝ) * (z - (15/16 : ℝ))^4 * (1 - z)^0 := by unfold in697_gap; ring
  linarith

theorem in697_gap_nonnegative (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ in697_gap z := by
  by_cases h0 : z ≤ (1/2 : ℝ)
  · exact in697_gap_interval_0 z hz h0
  by_cases h1 : z ≤ (3/4 : ℝ)
  · exact in697_gap_interval_1 z (by linarith) h1
  by_cases h2 : z ≤ (7/8 : ℝ)
  · exact in697_gap_interval_2 z (by linarith) h2
  by_cases h3 : z ≤ (29/32 : ℝ)
  · exact in697_gap_interval_3 z (by linarith) h3
  by_cases h4 : z ≤ (15/16 : ℝ)
  · exact in697_gap_interval_4 z (by linarith) h4
  exact in697_gap_interval_5 z (by linarith) hz1

theorem strong_euclidean_extension_exponent_gap_nonnegative (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (1 + (179 / 200 : ℝ))^2 * (1-z^2)^2 + (1 + (179 / 400 : ℝ))^2 * z^2 * (2-z^2) - (1/2 : ℝ) * (z+1)^2 * (2-z^2) := by
  simpa [in697_gap] using in697_gap_nonnegative z hz hz1
