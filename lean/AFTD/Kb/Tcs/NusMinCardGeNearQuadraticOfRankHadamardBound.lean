import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.NusExistsInclusionMinimalSubset
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsUnivZmod
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_ge_near_quadratic_of_rank_hadamard_bound

Topic: combinatorics   Node: 08e50804d31e

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

If every NUS set A ⊆ Z/pZ satisfies log p ≤ K(√|A| + |A|/log p)·log|A| with K ≥ 1, then m(p) ≥ (1/(32K²))(log p/log log p)² for every prime p ≥ 64. Consequently the target follows from the existence of such a K.
-/

lemma nus_min_card_ge_near_quadratic_of_rank_hadamard_bound_aux_real (K L n : ℝ)
    (hK : 1 ≤ K) (hL : 0 < L) (hM : 1 ≤ Real.log L) (hn : 2 ≤ n)
    (h : L ≤ K * (Real.sqrt n + n / L) * Real.log n) :
    1 / (32 * K ^ 2) * (L / Real.log L) ^ 2 ≤ n := by
  by_contra hcon
  have hn_lt : n < 1 / (32 * K ^ 2) * (L / Real.log L) ^ 2 := not_le.mp hcon
  have hlogL_pos : 0 < Real.log L := by linarith
  have hK_pos : 0 < K := by linarith
  have hn_pos : 0 < n := by linarith
  -- Step 1: log n < 2 * log L
  have h1 : 1 / (32 * K ^ 2) ≤ 1 := by
    have : (1 : ℝ) ≤ 32 * K ^ 2 := by nlinarith
    rw [div_le_one (by positivity)]
    exact this
  have h2 : (L / Real.log L) ^ 2 ≤ L ^ 2 := by
    rw [div_pow]
    have : (1 : ℝ) ≤ (Real.log L) ^ 2 := by nlinarith
    have : L ^ 2 / (Real.log L) ^ 2 ≤ L ^ 2 / 1 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) this
    linarith
  have hn_lt_Lsq : n < L ^ 2 := by
    calc n < 1 / (32 * K ^ 2) * (L / Real.log L) ^ 2 := hn_lt
    _ ≤ 1 * L ^ 2 := by nlinarith
    _ = L ^ 2 := by ring
  have hlog_lt : Real.log n < 2 * Real.log L := by
    have hlog_lt' : Real.log n < Real.log (L ^ 2) := Real.log_lt_log hn_pos hn_lt_Lsq
    have hlog_Lsq : Real.log (L ^ 2) = 2 * Real.log L := by
      rw [Real.log_pow L 2]
      ring
    linarith
  have hlogn_pos : 0 < Real.log n := by
    have : (1 : ℝ) < n := by linarith
    exact Real.log_pos this
  -- Step 2: sqrt bound
  have htarget_pos : 0 < L / (4 * K * Real.log L) := by positivity
  have hsq2 : (L / (4 * K * Real.log L)) ^ 2 = 1 / (16 * K ^ 2) * (L / Real.log L) ^ 2 := by ring
  have hlt : n < (L / (4 * K * Real.log L)) ^ 2 := by
    rw [hsq2]
    calc n < 1 / (32 * K ^ 2) * (L / Real.log L) ^ 2 := hn_lt
    _ < 1 / (16 * K ^ 2) * (L / Real.log L) ^ 2 := by
      apply mul_lt_mul_of_pos_right
      · have : 16 * K ^ 2 < 32 * K ^ 2 := by nlinarith
        have : (0 : ℝ) < 16 * K ^ 2 := by positivity
        exact div_lt_div_of_pos_left zero_lt_one this (by nlinarith)
      · have : 0 < L / Real.log L := div_pos hL hlogL_pos
        positivity
  have hsqrt : Real.sqrt n < L / (4 * K * Real.log L) := by
    have hs := Real.sqrt_lt_sqrt (by linarith) hlt
    rw [Real.sqrt_sq (le_of_lt htarget_pos)] at hs
    exact hs
  have hsqrt_term : K * Real.log n * Real.sqrt n < L / 2 := by
    have hlt1 : K * Real.log n * Real.sqrt n < K * (2 * Real.log L) * Real.sqrt n := by
      have : 0 < K * Real.sqrt n := by positivity
      nlinarith
    have hlt2 : 2 * K * Real.log L * Real.sqrt n < 2 * K * Real.log L * (L / (4 * K * Real.log L)) := by
      have : 0 < 2 * K * Real.log L := by positivity
      exact mul_lt_mul_of_pos_left hsqrt this
    have heq : 2 * K * Real.log L * (L / (4 * K * Real.log L)) = L / 2 := by
      have hK0 : K ≠ 0 := by linarith
      have hlog0 : Real.log L ≠ 0 := by linarith
      field_simp
      ring
    linarith
  -- Step 3: n/L bound
  have hlin_term : K * Real.log n * (n / L) < L / 16 := by
    have hpos : 0 < 2 * K * Real.log L / L := by positivity
    have hstep1 : 2 * K * Real.log L * (n / L) = (2 * K * Real.log L / L) * n := by ring
    have hbound : 2 * K * Real.log L * (n / L) < L / 16 := by
      rw [hstep1]
      calc (2 * K * Real.log L / L) * n < (2 * K * Real.log L / L) * (1 / (32 * K ^ 2) * (L / Real.log L) ^ 2) :=
          mul_lt_mul_of_pos_left hn_lt hpos
      _ = L / (16 * (K * Real.log L)) := by
        have h1 : K ≠ 0 := by linarith
        have h2 : Real.log L ≠ 0 := by linarith
        have h3 : L ≠ 0 := by linarith
        field_simp
        ring
      _ ≤ L / 16 := by
        have hKlog : 1 ≤ K * Real.log L := by nlinarith
        have hdenom : (16 : ℝ) ≤ 16 * (K * Real.log L) := by linarith
        exact div_le_div_of_nonneg_left (by linarith) (by positivity) hdenom
    have hstep2 : K * Real.log n * (n / L) ≤ 2 * K * Real.log L * (n / L) := by
      have : 0 < K * (n / L) := by positivity
      nlinarith
    linarith
  -- Step 4: combine
  have hcomb : K * (Real.sqrt n + n / L) * Real.log n < L := by
    calc K * (Real.sqrt n + n / L) * Real.log n = K * Real.log n * Real.sqrt n + K * Real.log n * (n / L) := by ring
    _ < L / 2 + L / 16 := add_lt_add hsqrt_term hlin_term
    _ = (9 / 16 : ℝ) * L := by ring
    _ < L := by linarith
  linarith

/-- Assembly step, fully proved modulo the rank-Hadamard estimate: a rank-Hadamard bound with constant K yields m(p) ≥ (1/(32K²))(log p/log log p)² for p ≥ 64. -/
theorem nus_min_card_ge_near_quadratic_of_rank_hadamard_bound (K : ℝ) (hK : 1 ≤ K)
    (hbound : ∀ (p : ℕ), p.Prime → ∀ A : Finset (ZMod p), finset_has_no_unique_sums A →
      Real.log p ≤ K * (Real.sqrt (A.card : ℝ) + (A.card : ℝ) / Real.log p) * Real.log (A.card : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → p.Prime →
      C * (Real.log p / Real.log (Real.log p)) ^ 2 ≤ (nus_min_card p : ℝ) := by
  refine ⟨1 / (32 * K ^ 2), by positivity, 64, fun p hp64 hpprime => ?_⟩
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst hp2
    omega
  have : Fact p.Prime := ⟨hpprime⟩
  have hne : {k | ∃ A : Finset (ZMod p), finset_has_no_unique_sums A ∧ A.card = k}.Nonempty :=
    ⟨(Finset.univ : Finset (ZMod p)).card, Finset.univ, finset_has_no_unique_sums_univ_zmod hpne2, rfl⟩
  obtain ⟨A, hA_nus, hA_card⟩ := Nat.sInf_mem hne
  have hn2 : 2 ≤ (nus_min_card p : ℝ) := by
    have hcard : 2 ≤ A.card := hA_nus.1
    rw [hA_card] at hcard
    exact_mod_cast hcard
  have hL_ge4 : 4 < Real.log (p : ℝ) := by
    have h1 : (64 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp64
    have h2 : Real.log 64 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) h1
    have h3 : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [h3, Real.log_pow] at h2
    have h4 := Real.log_two_gt_d9
    have h2' : (6 : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := h2
    linarith
  have hL_pos : 0 < Real.log (p : ℝ) := by linarith
  have hlogL : 1 ≤ Real.log (Real.log (p : ℝ)) := by
    have h4le : (4 : ℝ) ≤ Real.log (p : ℝ) := by linarith
    have hlog4 : Real.log 4 ≤ Real.log (Real.log (p : ℝ)) := Real.log_le_log (by norm_num) h4le
    have h4eq : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [h4eq, Real.log_pow] at hlog4
    have h4 := Real.log_two_gt_d9
    have hlog4' : (2 : ℝ) * Real.log 2 ≤ Real.log (Real.log (p : ℝ)) := hlog4
    linarith
  have hbound_A := hbound p hpprime A hA_nus
  rw [hA_card] at hbound_A
  exact nus_min_card_ge_near_quadratic_of_rank_hadamard_bound_aux_real K (Real.log (p : ℝ))
    (nus_min_card p : ℝ) hK hL_pos hlogL hn2 hbound_A
