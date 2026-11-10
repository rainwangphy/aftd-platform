import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber
import AFTD.Kb.Tcs.NumericalSemigroupMultiplicity

/-!
# numerical_semigroup_not_dvd_frobenius

Topic: combinatorics   Node: 7781acc8b324

Provenance: helper lemma. arXiv:2611.11559, Lemma 2.4

If S is a numerical semigroup with positive Frobenius number F and multiplicity m, then m does not divide F.
-/

/-- The multiplicity of a numerical semigroup cannot divide its Frobenius number. -/
theorem numerical_semigroup_not_dvd_frobenius (S : NumericalSemigroup) (F m : ℕ) (hF : 0 < F)
    (h_frob : numerical_semigroup_frobenius_number S = F)
    (h_mult : numerical_semigroup_multiplicity S = m) :
    ¬ m ∣ F := by
  -- The Frobenius number belongs to the complement of `S`.
  have hcompl_ne : ((S.toAddSubmonoid : Set ℕ)ᶜ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hzero : numerical_semigroup_frobenius_number S = 0 := by
      simp [numerical_semigroup_frobenius_number, hempty]
    omega
  have hF_compl : F ∈ ((S.toAddSubmonoid : Set ℕ)ᶜ) := by
    rw [← h_frob]
    exact Nat.sSup_mem hcompl_ne (Set.Finite.bddAbove S.finite_compl)
  have hF_notin : F ∉ (S.toAddSubmonoid : Set ℕ) := by
    simpa using hF_compl
  -- Some positive element lies in `S`, so the multiplicity is in `S`.
  let T : Set ℕ := {x ∈ (S.toAddSubmonoid : Set ℕ) | 0 < x}
  have hT_nonempty : T.Nonempty := by
    rcases (Set.Finite.bddAbove S.finite_compl) with ⟨N, hN⟩
    refine ⟨N + 1, ?_, Nat.succ_pos N⟩
    by_contra hmem
    have hcompl : N + 1 ∈ ((S.toAddSubmonoid : Set ℕ)ᶜ) := by
      simpa using hmem
    have hle : N + 1 ≤ N := hN hcompl
    omega
  have hm_eq : m = sInf T := by
    rw [← h_mult]
    rfl
  have hmT : m ∈ T := by
    rw [hm_eq]
    exact Nat.sInf_mem hT_nonempty
  have hmS : m ∈ (S.toAddSubmonoid : Set ℕ) := hmT.1
  -- If `m ∣ F`, then `F` is a multiple of an element of the additive monoid `S`.
  rintro ⟨k, hk⟩
  have hF_mem : F ∈ (S.toAddSubmonoid : Set ℕ) := by
    rw [hk]
    have hmem := AddSubmonoid.nsmul_mem S.toAddSubmonoid hmS k
    simpa [nsmul_eq_mul, mul_comm] using hmem
  exact hF_notin hF_mem
