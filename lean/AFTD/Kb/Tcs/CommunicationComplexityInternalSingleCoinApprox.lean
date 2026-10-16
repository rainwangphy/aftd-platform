import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceHasSumMeasureSingletons
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealPreimageFinset
import AFTD.Kb.Tcs.CommunicationComplexityUniformOnUnivMeasureRealEqCardFilter
import AFTD.Kb.Tcs.CommunicationComplexityInternalUniformApprox
import AFTD.Kb.Tcs.CommunicationComplexityInternalUniformApproxApprox
import AFTD.Kb.Tcs.CommunicationComplexityInternalCdfZero
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpacePi
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceBool

/-!
# CommunicationComplexity.Internal.single_coin_approx

Topic: communication   Node: f8d1e5304292

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.single_coin_approx`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Approximating a finite probability space by fair coin flips. Let $\Omega$ be a finite probability space, and let $\delta > 0$. Then there exist a
natural number $n$ and a map $\varphi : \mathrm{CoinTape}(n) \to \Omega$ from the
length-$n$ binary strings such that, writing $\mu_n$ for the uniform probability measure
on $\mathrm{CoinTape}(n)$ (each of the $2^n$ strings equally likely) and $\mu$ for the
probability measure on $\Omega$, every subset $S \subseteq \Omega$ satisfies
\[
  \mu_n\bigl(\varphi^{-1}(S)\bigr) \;\le\; \mu(S) + \delta.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- Every finite probability space is approximated by a coin tape: for any finite probability space `Ω` and any `δ > 0`, there exist `n` and a map `φ : CoinTape n → Ω` such that for every set `S ⊆ Ω`, the probability that `φ` of a uniformly random `n`-bit tape lies in `S` exceeds the probability of `S` by at most `δ`. This is the folklore discretisation step of Newman's theorem [New91]; no textbook statement of it was located. **Proof sketch.** Step 1: let `k = |Ω|` and choose `n` with `k / 2^n ≤ δ`. Step 2: let `N = 2^n = |CoinTape n|`, enumerate `Ω` as `Fin k` and transport the singleton masses of `Ω` to a PMF `q` on `Fin k`. Step 3: define `φ` as the composite of an enumeration `CoinTape n ≃ Fin N`, the map `uniformApprox q N : Fin N → Fin k`, and the inverse enumeration `Fin k ≃ Ω`. Step 4: for each point `i`, the fraction of tapes mapped to `i` is at most `q i + 1/N` (`uniformApprox_approx`, transported along the enumeration). Step 5: the number of tapes mapped into `S` is the sum of the fiber counts over the indices of `S`; the probability of the preimage is that count over `N`, and the probability of `S` is the sum of `q` over the indices of `S`. Step 6: summing the per-point bounds gives at most `vol S + |S| / N ≤ vol S + k / N ≤ vol S + δ`. -/
theorem CommunicationComplexity.Internal.single_coin_approx
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        volume.real (φ ⁻¹' S : Set (CoinTape n)) ≤
        volume.real S + δ := by
  classical
  haveI : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure (volume : Measure Ω)
  set k := Fintype.card Ω with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  haveI : NeZero k := ⟨by omega⟩
  -- Step 1: choose n with k / 2^n ≤ δ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℝ) / 2 ^ n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (Nat.cast_pos.mpr hk_pos)) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, le_of_lt ?_⟩
    have : (1 / 2 : ℝ) ^ n * k < δ := by rwa [lt_div_iff₀ (by positivity)] at hn
    linarith [show (k : ℝ) / 2 ^ n = (1 / 2) ^ n * k from by
      rw [one_div, inv_pow, inv_mul_eq_div]]
  use n
  set N := Fintype.card (CoinTape n)
  have hN_pos : 0 < N := Fintype.card_pos
  haveI : NeZero N := ⟨by omega⟩
  have hN_eq : N = 2 ^ n := by simp [N, Fintype.card_fin]
  -- Step 2: PMF on Fin k from the measure on Ω
  set e := Fintype.equivFin Ω
  have hpmf : HasSum (fun i : Fin k => volume ({e.symm i} : Set Ω)) 1 :=
    FiniteProbabilitySpace.hasSum_measure_singletons e
  set q : PMF (Fin k) := ⟨fun i => volume ({e.symm i} : Set Ω), hpmf⟩
  -- Step 3: φ: CoinTape n ≃ Fin N → uniformApprox → Fin k → e.symm → Ω
  set eC : CoinTape n ≃ Fin N := Fintype.equivFin _
  refine ⟨fun c => e.symm (uniformApprox q N (eC c)), fun S => ?_⟩
  set φ := fun c => e.symm (uniformApprox q N (eC c))
  set g := fun c : CoinTape n => uniformApprox q N (eC c)
  set S_idx := Finset.univ.filter (fun i : Fin k => e.symm i ∈ S)
  -- Step 4: per-element bound (bijected via eC)
  have helem : ∀ i : Fin k,
      ((Finset.univ.filter (fun c : CoinTape n => g c = i)).card : ℝ) / N ≤
      (q i).toReal + 1 / N := by
    intro i
    rw [show (Finset.univ.filter (fun c : CoinTape n => g c = i)).card =
      (Finset.univ.filter (fun j : Fin N => uniformApprox q N j = i)).card from
      Finset.card_equiv eC (fun c => by simp [g])]
    exact uniformApprox_approx q N i
  -- Step 5: fiber decomposition: {c | φ c ∈ S} partitions by g(c) value
  have hfiber : (Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card =
      ∑ i ∈ S_idx, (Finset.univ.filter (fun c : CoinTape n => g c = i)).card := by
    have : ∀ c : CoinTape n, φ c ∈ S ↔ g c ∈ S_idx := by
      intro c; simp [φ, g, S_idx]
    rw [show Finset.univ.filter (fun c => φ c ∈ S) =
      Finset.univ.filter (fun c => g c ∈ S_idx) from Finset.filter_congr (fun c _ => this c)]
    exact (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm
  -- CoinTape volume = counting / N
  have hvol_pre : volume.real (φ ⁻¹' S : Set (CoinTape n)) =
      ((Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card : ℝ) / N := by
    rw [measureReal_def]
    exact uniformOn_univ_measureReal_eq_card_filter
        (Ω := CoinTape n) (φ ⁻¹' S : Set (CoinTape n))
  -- Volume of S as sum of q
  have hvol_S : volume.real S = ∑ i ∈ S_idx, (q i).toReal := by
    have hpre : e ⁻¹' (↑S_idx : Set (Fin k)) = S := by
      ext x
      change (e x ∈ S_idx) ↔ x ∈ S
      simp [S_idx]
    rw [← hpre]
    rw [FiniteProbabilitySpace.measureReal_preimage_finset
      (Ξ := Ω) (Ω := Fin k) e S_idx]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hs : e ⁻¹' ({i} : Set (Fin k)) = ({e.symm i} : Set Ω) := by
      ext x
      constructor
      · intro hx
        simpa using congrArg e.symm hx
      · intro hx
        subst x
        exact e.apply_symm_apply i
    rw [hs]
    rfl
  -- Step 6: combine
  rw [hvol_pre, hfiber]; push_cast
  have hN_pos_real : (0 : ℝ) < N := by positivity
  -- (∑ f_i) / N ≤ vol(S) + δ, using per-element bound
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos_real
  calc (∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ)) / N
      = ∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ) / N := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    _ ≤ ∑ i ∈ S_idx, ((q i).toReal + 1 / N) :=
        Finset.sum_le_sum (fun i _ => helem i)
    _ = (∑ i ∈ S_idx, (q i).toReal) + S_idx.card / N := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ volume.real S + k / N := by
        rw [hvol_S]
        have hcard : (S_idx.card : ℝ) ≤ k := by
          have h := S_idx.card_le_univ; simp only [Fintype.card_fin] at h; exact_mod_cast h
        linarith [div_le_div_of_nonneg_right hcard hN_pos_real.le]
    _ ≤ volume.real S + δ := by
        have : (k : ℝ) / N ≤ δ := by rw [hN_eq]; push_cast; exact hn
        linarith
