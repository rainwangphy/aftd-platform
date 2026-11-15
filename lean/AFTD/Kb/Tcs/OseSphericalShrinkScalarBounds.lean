import AFTD.Prelude
import AFTD.Kb.Tcs.OseCubeScalarCertificate

/-!
# ose_spherical_shrink_scalar_bounds

Topic: algorithms   Node: a6ba2bbf9755

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; scalar estimates for the proposed spherical construction

Under the small-s parameter assumptions for the spherical two-layer construction, the two radial scaling factors have the ordering and cross-distance bounds required to attain distortion q.
-/

theorem ose_spherical_shrink_scalar_bounds (q r s : ℝ) (hq : 0 < q) (hq2 : 2 ≤ q ^ 2) (hr : 0 < r) (hs : 0 < s) (hid : s ^ 2 + 2 * r * s = 1) (hsmall : s * q ≤ 1) : let α := s * q; let β := min q (1 / α); 1 ≤ q ∧ 0 < α ∧ α ≤ 1 ∧ 1 ≤ β ∧ β ≤ q ∧ α * β ≤ 1 ∧ (β - α)^2 ≤ 4 * r^2 ∧ r^2 + q^2 * (1 - α * β) ≤ q^2 * r^2 := by
  have hcert (p u : ℝ) (hp : 2 ≤ p) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :=
    ose_cube_scalar_certificate p u hp hu0 hu1
  dsimp only
  have hq1 : 1 ≤ q := by nlinarith
  have ha : 0 < s*q := mul_pos hs hq
  have hbeta1 : 1 ≤ min q (1 / (s*q)) :=
    le_min hq1 ((le_div_iff₀ ha).2 (by simpa using hsmall))
  have hbetaq : min q (1 / (s*q)) ≤ q := min_le_left _ _
  have hbetainv : min q (1 / (s*q)) ≤ 1 / (s*q) := min_le_right _ _
  have hab : (s*q) * min q (1 / (s*q)) ≤ 1 := by
    calc (s*q) * min q (1 / (s*q)) ≤ (s*q) * (1 / (s*q)) :=
          mul_le_mul_of_nonneg_left hbetainv (le_of_lt ha)
      _ = 1 := by field_simp [ne_of_gt ha]
  have hsec : 1 ≤ (s*q)*(2*r+s*q) := by
    have hp := mul_nonneg (show 0 ≤ q-1 by linarith) (show 0 ≤ 1+q*s^2 by positivity)
    have hmul := congrArg (fun z : ℝ => q * z) hid
    nlinarith [hp, hmul]
  have hinv : 1 / (s*q) ≤ 2*r+s*q := (div_le_iff₀ ha).2 (by simpa [mul_comm] using hsec)
  have hdiff0 : 0 ≤ min q (1 / (s*q)) - s*q := by linarith
  have hdiff : min q (1 / (s*q)) - s*q ≤ 2*r := by linarith
  have hdiffsq : (min q (1 / (s*q)) - s*q)^2 ≤ 4*r^2 := by
    have h := pow_le_pow_left₀ hdiff0 hdiff 2
    nlinarith
  refine ⟨hq1, ha, hsmall, hbeta1, hbetaq, hab, hdiffsq, ?_⟩
  by_cases hu : 1 ≤ s*q^2
  · have hb : min q (1 / (s*q)) = 1 / (s*q) := by
      apply min_eq_right
      apply (div_le_iff₀ ha).2
      nlinarith [hu]
    rw [hb]
    have hprod : (s*q) * (1 / (s*q)) = 1 := by field_simp [ne_of_gt ha]
    rw [hprod]
    nlinarith [sq_nonneg r]
  · have hu_le : s*q^2 ≤ 1 := by linarith
    have hb : min q (1 / (s*q)) = q := by
      apply min_eq_left
      apply (le_div_iff₀ ha).2
      nlinarith [hu_le]
    rw [hb]
    let p : ℝ := q^2
    let u : ℝ := s*p
    have hp : 2 ≤ p := hq2
    have hp0 : 0 < p := by linarith
    have hu0 : 0 < u := mul_pos hs hp0
    have hu1 : u ≤ 1 := by dsimp [u,p]; exact hu_le
    have hcert' := hcert p u hp (le_of_lt hu0) hu1
    have hpuid : p^2-u^2 = 2*p*u*r := by
      have hrel : 1-s^2 = 2*r*s := by nlinarith [hid]
      calc p^2-u^2 = (q^2)^2 * (1-s^2) := by dsimp [p,u]; ring
        _ = (q^2)^2 * (2*r*s) := by rw [hrel]
        _ = 2*p*u*r := by dsimp [p,u]; ring
    rw [hpuid] at hcert'
    have hf : 0 < 4*p^2*u^2 := by positivity
    have hfactor : (4*p^2*u^2) * (p*(1-u)) ≤
        (4*p^2*u^2) * ((p-1)*r^2) := by nlinarith [hcert']
    have hresult := le_of_mul_le_mul_left hfactor hf
    dsimp [p,u] at hresult
    nlinarith [hresult]
