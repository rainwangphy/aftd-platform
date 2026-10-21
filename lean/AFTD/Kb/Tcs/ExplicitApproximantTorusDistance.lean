import AFTD.Prelude
import AFTD.Kb.Tcs.ExplicitApproximant
import AFTD.Kb.Tcs.TorusDistance
import AFTD.Kb.Tcs.ExplicitError
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.ParityCharacter
import AFTD.Kb.Tcs.TopCoefficient
import AFTD.Kb.Tcs.AcceptingCount
import AFTD.Kb.Tcs.FullMonomial

/-!
# explicitApproximant_torusDistance

Topic: circuits   Node: 602b49f74233

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.14

For any Boolean function f : (Fin n → Bool) → Bool on n > 0 variables and any x : Fin n → Bool, torusDistance (explicitApproximant f x - bit (f x) / 2) equals explicitError f.
-/

open scoped BigOperators

/-- Every product of the ±1 factors `if x i = true then 1 else -1` is `1` or `-1`. -/
lemma explicitApproximant_torusDistance_chi_int_pm {n : ℕ} (x : Fin n → Bool) :
    (∏ i, if x i = true then (1:ℤ) else -1) = 1 ∨ (∏ i, if x i = true then (1:ℤ) else -1) = -1 := by
  have key : ∀ s : Finset (Fin n),
      (∏ i ∈ s, if x i = true then (1:ℤ) else -1) = 1 ∨ (∏ i ∈ s, if x i = true then (1:ℤ) else -1) = -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with h | h <;>
        rcases (show (if x a = true then (1:ℤ) else -1) = 1 ∨ (if x a = true then (1:ℤ) else -1) = -1 from by split <;> simp) with h' | h' <;>
          rw [h', h] <;> norm_num
  simpa using key Finset.univ

/-- The top Fourier coefficient and the accepting count of `f` have the same parity. -/
lemma explicitApproximant_torusDistance_topCoefficient_emod_two {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    topCoefficient f % 2 = (acceptingCount f : ℤ) % 2 := by
  have hsum : (∑ x : Fin n → Bool, (if f x = true then (1:ℤ) else 0)) = (acceptingCount f : ℤ) := by
    rw [Finset.sum_boole]
    rw [acceptingCount, Fintype.card_subtype]
  have hdvd : (2:ℤ) ∣ topCoefficient f - (acceptingCount f : ℤ) := by
    have hsplit : topCoefficient f - (acceptingCount f : ℤ)
        = ∑ x : Fin n → Bool,
            ((if f x = true then ∏ i, (if x i = true then (1:ℤ) else -1) else 0)
              - (if f x = true then (1:ℤ) else 0)) := by
      rw [Finset.sum_sub_distrib, hsum]
      rfl
    rw [hsplit]
    refine Finset.dvd_sum ?_
    intro y _
    by_cases h : f y = true
    · rw [if_pos h, if_pos h]
      rcases explicitApproximant_torusDistance_chi_int_pm y with hc | hc <;> rw [hc] <;> norm_num
    · rw [if_neg h, if_neg h]
      simp
  exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd hdvd)

/-- The parity character takes only the values `1` and `-1`. -/
lemma explicitApproximant_torusDistance_parityCharacter_pm {n : ℕ} (x : Fin n → Bool) :
    parityCharacter x = 1 ∨ parityCharacter x = -1 := by
  rw [parityCharacter]
  have key : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (if x i = true then (1:ℝ) else -1)) = 1 ∨ (∏ i ∈ s, (if x i = true then (1:ℝ) else -1)) = -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with h | h <;>
        rcases (show (if x a = true then (1:ℝ) else -1) = 1 ∨ (if x a = true then (1:ℝ) else -1) = -1 from by split <;> simp) with h' | h' <;>
          rw [h', h] <;> norm_num
  simpa using key Finset.univ

/-- The full monomial at a Boolean point is `0` or `1`. -/
lemma explicitApproximant_torusDistance_fullMonomial_zero_or_one {n : ℕ} (x : Fin n → Bool) :
    fullMonomial x = 0 ∨ fullMonomial x = 1 := by
  by_cases h : ∀ i, x i = true
  · right
    rw [fullMonomial]
    refine Finset.prod_eq_one ?_
    intro i _
    rw [h i]
    simp [bit]
  · left
    push Not at h
    obtain ⟨i, hi⟩ := h
    rw [fullMonomial]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [bit, hi]

/-- Shifting by an integer does not change the distance to the nearest integer. -/
lemma explicitApproximant_torusDistance_add_int (u : ℝ) (m : ℤ) :
    torusDistance (u + (m:ℝ)) = torusDistance u := by
  unfold torusDistance
  rw [round_add_intCast]
  congr 1
  push_cast
  ring

/-- Pointwise torus error of the explicit approximant at every Boolean point. -/
theorem explicitApproximant_torusDistance {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    torusDistance (explicitApproximant f x - bit (f x) / 2) = explicitError f := by
  have hsub : explicitApproximant f x - bit (f x) / 2
      = -(↑(topCoefficient f / 2) * fullMonomial x)
          - ↑(topCoefficient f % 2) * parityCharacter x / 2 ^ (n + 1) := by
    simp only [explicitApproximant, bit]
    ring
  rw [hsub]
  set r := topCoefficient f % 2 with hrdef
  set k := topCoefficient f / 2 with hkdef
  have hint : ∃ m : ℤ, (-(↑k * fullMonomial x) - ↑r * parityCharacter x / 2 ^ (n + 1))
      = (-(↑r * parityCharacter x / 2 ^ (n + 1))) + (m : ℝ) := by
    rcases explicitApproximant_torusDistance_fullMonomial_zero_or_one x with h | h
    · refine ⟨0, ?_⟩
      rw [h]
      push_cast
      ring
    · refine ⟨-k, ?_⟩
      rw [h]
      push_cast
      ring
  obtain ⟨m, hm⟩ := hint
  rw [hm, explicitApproximant_torusDistance_add_int]
  have hpow : (4:ℝ) ≤ 2 ^ (n + 1) := by
    have h2 : 2 ≤ n + 1 := by omega
    calc (4:ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) h2
  have hpos : (0:ℝ) < 2 ^ (n + 1) := by positivity
  have hr01 : r = 0 ∨ r = 1 := Int.emod_two_eq_zero_or_one (topCoefficient f)
  have hrnn : (0:ℝ) ≤ (r:ℝ) := by rcases hr01 with h | h <;> rw [h] <;> norm_num
  have hrle : (r:ℝ) ≤ 1 := by rcases hr01 with h | h <;> rw [h] <;> norm_num
  have hχabs : |parityCharacter x| = 1 := by
    rcases explicitApproximant_torusDistance_parityCharacter_pm x with h | h <;> rw [h] <;> norm_num
  have habs : |-(↑r * parityCharacter x / 2 ^ (n + 1))| = (r:ℝ) / 2 ^ (n + 1) := by
    rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hrnn, hχabs, abs_of_pos hpos]
    ring
  have hlt : |-(↑r * parityCharacter x / 2 ^ (n + 1))| < 1 / 2 := by
    rw [habs, div_lt_iff₀ hpos]
    nlinarith
  have hrnd : round (-(↑r * parityCharacter x / 2 ^ (n + 1))) = 0 := by
    rw [round_eq_zero_iff]
    rw [abs_lt] at hlt
    exact ⟨by linarith, hlt.2⟩
  have hval : torusDistance (-(↑r * parityCharacter x / 2 ^ (n + 1))) = (r:ℝ) / 2 ^ (n + 1) := by
    unfold torusDistance
    rw [hrnd]
    simp only [Int.cast_zero, sub_zero]
    exact habs
  rw [hval]
  have hpar : r = (acceptingCount f : ℤ) % 2 := by
    rw [hrdef]
    exact explicitApproximant_torusDistance_topCoefficient_emod_two f
  have hcast : Odd ((acceptingCount f : ℤ)) ↔ Odd (acceptingCount f) := by
    have hem : ((↑(acceptingCount f) : ℤ) % 2) = (↑(acceptingCount f % 2) : ℤ) := by
      have hh := Int.natCast_emod (acceptingCount f) 2
      simpa using hh
    rw [Int.odd_iff, Nat.odd_iff, hem]
    exact Nat.cast_eq_one
  have hodd : Odd (acceptingCount f) ↔ r = 1 := by
    rw [hpar, ← hcast, Int.odd_iff]
  unfold explicitError
  by_cases ho : Odd (acceptingCount f)
  · rw [if_pos ho, hodd.mp ho]
    push_cast
    ring
  · rw [if_neg ho]
    rcases hr01 with h | h
    · rw [h]; norm_num
    · exact absurd h (fun hh => ho (hodd.mpr hh))
