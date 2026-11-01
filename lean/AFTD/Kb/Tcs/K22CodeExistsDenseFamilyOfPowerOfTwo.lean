import AFTD.Prelude
import AFTD.Kb.Tcs.CardSimpleGraph
import AFTD.Kb.Tcs.K22CodeMaxDensityTwoPowGe
import AFTD.Kb.Tcs.IsKstCode

/-!
# k22_code_exists_dense_family_of_power_of_two

Topic: combinatorics   Node: b6ad778dff0f

Provenance: helper lemma. step towards k22_code_exists_dense_family

For every natural number r ≥ 2, there exists a K_{2,2}-code on Fin (2^r) with density at least 1 / 2^r.
-/

/-- There exists a K_{2,2}-code on Fin (2^r) with density at least 1 / 2^r for all r ≥ 2. -/
theorem k22_code_exists_dense_family_of_power_of_two (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : Set (SimpleGraph (Fin (2 ^ r))),
      is_kst_code 2 2 (2 ^ r) C ∧
      1 / ((2 : ℝ) ^ r) ≤ (C.ncard : ℝ) / (2 ^ ((2 ^ r).choose 2) : ℝ) := by
  classical
  letI : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 r) = 2 ^ r := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 r (by omega)
  have hcardV : Fintype.card (Fin (2 ^ r)) = 2 ^ r := Fintype.card_fin _
  let e : Fin (2 ^ r) ≃ GaloisField 2 r := (Fintype.equivFinOfCardEq hcard).symm
  set N := (2 ^ r).choose 2 with hN
  have hrN := k22_code_max_density_two_pow_ge_r_le_choose r hr
  obtain ⟨s, hs⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := k22_code_max_density_two_pow_ge_sig (fun v => e v)) (n := 2 ^ (N - r)) (by
      rw [hcard, card_simpleGraph, hcardV, ← pow_add, Nat.add_sub_cancel' hrN])
  refine ⟨{G | k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s}, ?_, ?_⟩
  · exact k22_code_max_density_two_pow_ge_fiber_code _ e.injective s
  · have hncard : 2 ^ (N - r) ≤
        ({G : SimpleGraph (Fin (2 ^ r)) | k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s} : Set _).ncard := by
      have : {G : SimpleGraph (Fin (2 ^ r)) | k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s}
          = ↑(Finset.univ.filter fun G => k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s) := by
        ext G; simp
      rw [this, Set.ncard_coe_finset]
      exact hs
    have hpos : (0 : ℝ) < 2 ^ N := by positivity
    rw [div_le_div_iff₀ (by positivity) hpos, one_mul]
    calc (2 : ℝ) ^ N = (2 : ℝ) ^ (N - r) * 2 ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hrN]
      _ ≤ (({G : SimpleGraph (Fin (2 ^ r)) | k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s} : Set _).ncard : ℝ) * 2 ^ r := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hncard
