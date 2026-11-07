import AFTD.Prelude
import AFTD.Kb.Tcs.CanCertifyNoiselessCodes
import AFTD.Kb.Tcs.IsJointlyMeasurableOn
import AFTD.Kb.Tcs.CertifiesNoiselessCodes

/-!
# not_can_certify_noiseless_codes_one

Topic: quantum   Node: 4b1e36c7ff35

Provenance: original. Related work: arXiv:2610.37347

For any dimension d, a single binary measurement cannot certify noiseless quantum codes, so ¬ can_certify_noiseless_codes d 1 holds.
-/

/-- For any dimension d, no single binary measurement can certify noiseless quantum codes. -/
theorem not_can_certify_noiseless_codes_one (d : ℕ) : ¬ can_certify_noiseless_codes d 1 := by
  intro h
  rcases h with ⟨M, s_max, hs_max, hpos, hjm, -⟩
  have hs_max_in : s_max ∈ Set.Icc 0 s_max := ⟨by linarith, le_refl _⟩
  have hjm_smax := (hjm s_max hs_max_in).mp
  have hjm_holds : is_jointly_measurable_on (M s_max) 1 := by
    use fun f => if f 0 then M s_max 0 else 1 - M s_max 0
    refine ⟨?_, ?_, ?_⟩
    · intro f
      dsimp
      split_ifs
      · exact (hpos s_max hs_max_in 0).1
      · exact (hpos s_max hs_max_in 0).2
    · rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
      simp
    · intro j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
      simp
  have h_le := hjm_smax hjm_holds
  linarith
