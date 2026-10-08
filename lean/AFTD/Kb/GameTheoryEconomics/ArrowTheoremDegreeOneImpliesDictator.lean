import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremIsDictator
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremUnanimity
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisDictatorEqChi
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisIsOddFunc
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne
import AFTD.Kb.Tcs.BooleanAnalysisParsevalPmOne
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot

/-!
# ArrowTheorem.degree_one_implies_dictator

Topic: social_choice   Node: 58a3cff73a2e

Provenance: helper lemma. TCSlib, `ArrowTheorem.degree_one_implies_dictator`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Degree-one unanimous voting rules are dictatorships. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function that is odd, is $\pm 1$-valued, and is
unanimous. Suppose further that $f$ has degree one, in the sense that its Fourier--Walsh
coefficient $\hat f(S)$ vanishes for every set $S\subseteq[n]$ with $\abs{S}\neq 1$.
Then $f$ is a dictatorship: there is a coordinate $i$ with $f=\mathrm{dict}_i$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- A ±1-valued odd unanimous function with all Fourier weight on level 1 is a dictator. Proof: f = ∑_i a_i · χ_{i} with ∑_i a_i² = 1 (Parseval). - Unanimity: f(false,...,false) = ∑_i a_i = 1. - For each j: f(only-j-true) = 1 - 2·a_j ∈ {-1,1}, so a_j ∈ {0,1}. - From a_j ∈ {0,1} and ∑ a_j² = ∑ a_j = 1: exactly one a_{j₀} = 1. - Hence f = χ_{{j₀}} = dictator j₀. **Source:** [OD14, Ch. 2]. -/
lemma ArrowTheorem.degree_one_implies_dictator (f : BooleanFunc n) (_hodd : isOddFunc f)
    (hpm : isPmOne f) (huniv : unanimity f)
    (hdeg1 : ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0) :
    isDictator f := by
  -- Step 1: Parseval gives ∑_i f̂({i})² = 1
  -- All non-singleton Fourier coefficients are 0 by hdeg1.
  have hpars : ∑ i : Fin n, fourierCoeff f {i} ^ 2 = 1 := by
    have hparseval := parseval_pm_one f hpm
    -- Reindex via Finset.sum_image: ∑_i f({i})² = ∑_{S ∈ image} f(S)² = ∑_S f(S)²
    have hexpand : ∑ i : Fin n, fourierCoeff f ({i} : Finset (Fin n)) ^ 2 =
        ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
      rw [← Finset.sum_image (f := fun S => fourierCoeff f S ^ 2)
              (fun i _ j _ h => Finset.singleton_injective h)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : S.card ≠ 1 := by
        intro hc
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        exact hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
      simp [hdeg1 S hcard]
    rw [hexpand, hparseval]
  -- Step 2: Walsh expansion restricted to level 1
  -- f(x) = ∑_i f̂({i}) · boolToSign(x i)
  have hfourier : ∀ x : BoolCube n,
      f x = ∑ i : Fin n, fourierCoeff f {i} * boolToSign (x i) := by
    intro x
    rw [walsh_expansion f x]
    -- Reduce full sum to singleton terms (non-singletons vanish)
    have step1 : ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).image (fun i => ({i} : Finset (Fin n))),
            fourierCoeff f S * chiS S x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : S.card ≠ 1 := by
        intro hc
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        exact hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
      simp [hdeg1 S hcard]
    -- Reindex image sum over Fin n
    have step2 : ∑ S ∈ (Finset.univ : Finset (Fin n)).image (fun i => ({i} : Finset (Fin n))),
        fourierCoeff f S * chiS S x =
        ∑ i : Fin n, fourierCoeff f {i} * boolToSign (x i) := by
      rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
      congr 1; ext i; rw [chiS_singleton]
    rw [step1, step2]
  -- Step 3: Unanimity gives ∑_i a_i = 1
  have huniv' : ∑ i : Fin n, fourierCoeff f {i} = 1 := by
    have h := huniv
    rw [unanimity] at h
    rw [hfourier] at h
    simp only [boolToSign_false, mul_one] at h
    exact h
  -- Step 4: For each i, f(only-i-true) ∈ {-1,1} gives a_i ∈ {0,1}
  have hai_range : ∀ i : Fin n, fourierCoeff f {i} = 0 ∨ fourierCoeff f {i} = 1 := by
    intro i
    -- f at x with only bit i = true equals 1 - 2·a_i
    have hval : f (Function.update (fun _ => false) i true) =
        1 - 2 * fourierCoeff f {i} := by
      rw [hfourier]
      have key : ∑ j : Fin n,
          fourierCoeff f {j} * boolToSign ((Function.update (fun _ => false) i true) j) =
          -(fourierCoeff f {i}) + ∑ j ∈ Finset.univ.erase i, fourierCoeff f {j} := by
        rw [← Finset.add_sum_erase Finset.univ
            (fun j => fourierCoeff f {j} * boolToSign ((Function.update (fun _ => false) i true) j))
            (Finset.mem_univ i)]
        simp only [Function.update_apply, ↓reduceIte,
                   boolToSign_true, mul_neg, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hjni : j ≠ i := (Finset.mem_erase.mp hj).1
        simp only [if_neg hjni, boolToSign_false, mul_one]
      rw [key]
      have herase := Finset.add_sum_erase Finset.univ
          (fun j => fourierCoeff f {j}) (Finset.mem_univ i)
      linarith [huniv']
    have hpm_val := hpm (Function.update (fun _ => false) i true)
    rw [hval] at hpm_val
    rcases hpm_val with h | h
    · left; linarith
    · right; linarith
  -- Step 5: Exactly one a_{j₀} = 1, the rest are 0
  -- Using |{i | a_i = 1}| = ∑_{i∈J} 1 = ∑_i a_i = 1
  have hexists : ∃ j : Fin n, fourierCoeff f {j} = 1 ∧
      ∀ i : Fin n, i ≠ j → fourierCoeff f {i} = 0 := by
    let J := Finset.univ.filter (fun i : Fin n => fourierCoeff f {i} = 1)
    have hJ_card : J.card = 1 := by
      have hcard_real : (J.card : ℝ) = 1 := by
        have h0 : ∀ i : Fin n, i ∉ J → fourierCoeff f {i} = 0 := by
          intro i hi
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          push_neg at hi
          rcases hai_range i with h | h
          · exact h
          · exact absurd h hi
        calc (J.card : ℝ)
            = ∑ i ∈ J, (1 : ℝ) := by simp
          _ = ∑ i ∈ J, fourierCoeff f {i} := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ((Finset.mem_filter.mp hi).2).symm
          _ = ∑ i : Fin n, fourierCoeff f {i} := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro i _ hi
              exact h0 i hi
          _ = 1 := huniv'
      exact_mod_cast hcard_real
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hJ_card
    have hj_mem : j ∈ J := by rw [hj]; exact Finset.mem_singleton_self j
    refine ⟨j, (Finset.mem_filter.mp hj_mem).2, fun i hi => ?_⟩
    rcases hai_range i with h | h
    · exact h
    · exfalso
      have hi_mem : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hj] at hi_mem
      exact hi (Finset.mem_singleton.mp hi_mem)
  obtain ⟨j₀, hj₀, hothers⟩ := hexists
  -- Step 6: f = χ_{{j₀}} = dictator j₀
  use j₀
  ext x
  rw [hfourier x, dictator_eq_chi, chiS_singleton]
  -- ∑_i a_i * boolToSign(x i) = boolToSign(x j₀) since a_{j₀}=1 and a_i=0 for i≠j₀
  conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  simp only [hj₀, one_mul]
  suffices h : ∑ i ∈ Finset.univ.erase j₀, fourierCoeff f {i} * boolToSign (x i) = 0 by
    linarith
  apply Finset.sum_eq_zero
  intro i hi
  simp [hothers i (Finset.mem_erase.mp hi).1]
