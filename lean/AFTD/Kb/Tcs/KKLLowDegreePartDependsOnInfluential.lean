import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisInfluence
import AFTD.Kb.Tcs.BooleanAnalysisInfluenceEqSumFourier
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisParseval
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.KKLIsJunta
import AFTD.Kb.Tcs.KKLInfluentialCoords
import AFTD.Kb.Tcs.KKLL2DistSq
import AFTD.Kb.Tcs.KKLLowDegreePart
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.G

/-!
# KKL.lowDegreePart_depends_on_influential

Topic: combinatorics   Node: c9d1c5769124

Provenance: helper lemma. TCSlib, `KKL.lowDegreePart_depends_on_influential`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Low-degree part is close to a junta on the influential coordinates. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function, let $k$ be a natural number, and let
$\tau>0$. Then there is a Boolean function $g:\{0,1\}^n\to\bbr$ that is a junta on the
set $J_\tau(f)=\{\,i\in[n]:\mathrm{Inf}_i[f]\ge\tau\,\}$ of $\tau$-influential
coordinates and that approximates the low-degree part $f_{\le k}$ in squared $L^2$
distance, namely
\[
  \E\big[(f_{\le k}(x)-g(x))^2\big]\;\le\;n\,\tau,
\]
where the expectation is taken under the uniform measure on the cube.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.lowDegreePart_depends_on_influential (f : BooleanFunc n) (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : BooleanFunc n,
      IsJunta g (influentialCoords f τ) ∧
      l2DistSq (lowDegreePart f k) g ≤ (n : ℝ) * τ := by
  let J := influentialCoords f τ
  let g : BooleanFunc n := fun x =>
    ∑ S : Finset (Fin n),
      if S.card ≤ k ∧ S ⊆ J then fourierCoeff f S * chiS S x else 0
  refine ⟨g, ?_, ?_⟩
  -- Part 1: IsJunta g J
  · intro x y hxy
    simp only [g]
    apply Finset.sum_congr rfl; intro S _
    split_ifs with h
    · congr 1; simp only [chiS]
      apply Finset.prod_congr rfl; intro i hi
      exact congrArg boolToSign (hxy i (h.2 hi))
    · rfl
  -- Part 2: l2DistSq (lowDegreePart f k) g ≤ n * τ
  · -- The difference lowDegreePart f k - g keeps only S with |S|≤k and S⊄J
    -- By Parseval, l2DistSq = ∑_{|S|≤k, S⊄J} fhat(S)^2
    -- Bound: ≤ ∑_{S⊄J} fhat(S)^2 ≤ ∑_{i∉J} ∑_{S∋i} fhat(S)^2 = ∑_{i∉J} Inf_i < n*τ
    -- We use a direct bound: l2DistSq ≤ innerProduct of the difference
    -- Step 1: Express the difference pointwise
    have hdiff : ∀ x, lowDegreePart f k x - g x =
        ∑ S : Finset (Fin n),
          if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0 := by
      intro x
      simp only [lowDegreePart, g]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro S _
      by_cases h1 : S.card ≤ k <;> by_cases h2 : S ⊆ J <;> simp [h1, h2]
    -- Step 2: l2DistSq = innerProduct of difference = Parseval sum
    -- We bound l2DistSq directly
    have hbound : l2DistSq (lowDegreePart f k) g ≤
        ∑ S : Finset (Fin n),
          if ¬S ⊆ J then fourierCoeff f S ^ 2 else 0 := by
      simp only [l2DistSq]
      rw [show (fun x => (lowDegreePart f k x - g x) ^ 2) =
          (fun x => ((∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0)) ^ 2) from
        funext (fun x => by rw [hdiff x])]
      -- The expect of squares of a Fourier sum = sum of squared coefficients (Parseval)
      -- This is: innerProduct h h = ∑_S (fourierCoeff h S)^2 where h is the diff
      -- h = ∑_{|S|≤k, S⊄J} fhat(S) * chiS S
      -- By Parseval: expect(h^2) = ∑_S (fourierCoeff h S)^2
      -- But fourierCoeff h S = fhat(S) when |S|≤k ∧ S⊄J, else 0
      -- So expect(h^2) = ∑_{|S|≤k, S⊄J} fhat(S)^2
      -- Then ≤ ∑_{S⊄J} fhat(S)^2 by adding nonneg terms
      -- Define h before using it
      set h : BooleanFunc n := fun x => ∑ S : Finset (Fin n),
          if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0
      -- Step 1: expect(h^2) = innerProduct h h = ∑ fourierCoeff h S ^ 2
      have hh_eq : expect (fun x => (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0) ^ 2) =
          ∑ S : Finset (Fin n), fourierCoeff h S ^ 2 := by
        have inner_eq : expect (fun x => h x ^ 2) = innerProduct h h := by
          simp only [innerProduct]; congr 1; ext x; ring
        have goal_eq : expect (fun x => (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0) ^ 2) =
            expect (fun x => h x ^ 2) := rfl
        rw [goal_eq, inner_eq, parseval]
      rw [hh_eq]
      -- Step 2: Compute Fourier coefficients of h (same as fourierCoeff_lowDegreePart pattern)
      have hcoeff : ∀ T : Finset (Fin n),
          fourierCoeff h T = if T.card ≤ k ∧ ¬T ⊆ J then fourierCoeff f T else 0 := by
        intro T
        simp only [h]
        unfold BooleanAnalysis.fourierCoeff innerProduct expect
        beta_reduce
        set w := uniformWeight n
        set fhat : Finset (Fin n) → ℝ := fun S => w * ∑ y, f y * chiS S y
        -- Rearrange: w * ∑ x, (∑ S, if ... then fhat S * χ_S x else 0) * χ_T x
        have step1 : w * ∑ x, (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fhat S * chiS S x else 0) * chiS T x =
            ∑ S : Finset (Fin n), if S.card ≤ k ∧ ¬S ⊆ J then
              fhat S * (w * ∑ x, chiS S x * chiS T x) else 0 := by
          rw [Finset.mul_sum]
          conv_lhs => arg 2; ext x; rw [Finset.sum_mul]
          simp_rw [show ∀ (S : Finset (Fin n)) (x : BoolCube n),
              (if S.card ≤ k ∧ ¬S ⊆ J then fhat S * chiS S x else 0) * chiS T x =
              (if S.card ≤ k ∧ ¬S ⊆ J then fhat S * (chiS S x * chiS T x) else 0) from by
            intros; split_ifs <;> ring]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1; ext S
          split_ifs with hS
          · congr 1; ext x; ring
          · simp
        rw [step1]
        have ortho : ∀ S : Finset (Fin n),
            w * ∑ x, chiS S x * chiS T x = if S = T then 1 else 0 := by
          intro S
          have := fourier_coeff_chi S T
          simp only [innerProduct, expect] at this
          exact this
        simp_rw [ortho]
        simp only [mul_ite, mul_one, mul_zero]
        conv_lhs => arg 2; ext S; rw [show (if S.card ≤ k ∧ ¬S ⊆ J then
            (if S = T then fhat S else 0) else 0) =
            (if S = T then (if T.card ≤ k ∧ ¬T ⊆ J then fhat T else 0) else 0) from by
          split_ifs <;> simp_all]
        simp [Finset.sum_ite_eq', fhat]
      -- Step 3: Rewrite the Parseval sum using hcoeff
      conv_lhs => arg 2; ext S; rw [hcoeff S]
      -- Step 4: (if cond then c else 0)^2 = if cond then c^2 else 0
      conv_lhs => arg 2; ext S; rw [show (if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S else 0) ^ 2 =
          (if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S ^ 2 else 0) from by
        split_ifs <;> simp [sq]]
      -- Step 5: ∑_S (if |S|≤k ∧ S⊄J then fhat^2 else 0) ≤ ∑_S (if S⊄J then fhat^2 else 0)
      apply Finset.sum_le_sum
      intro S _
      by_cases hSJ : S ⊆ J
      · simp [hSJ]
      · by_cases hk : S.card ≤ k
        · simp [hk, hSJ]
        · simp only [hSJ, hk, not_false_eq_true, ↓reduceIte, false_and]
          exact sq_nonneg (fourierCoeff f S)
    -- Step 3: Union bound: ∑_{S⊄J} fhat(S)^2 ≤ ∑_{i∉J} Inf_i[f]
    have hunion : ∑ S : Finset (Fin n), (if ¬S ⊆ J then fourierCoeff f S ^ 2 else 0) ≤
        ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f := by
      -- Rewrite RHS using influence_eq_sum_fourier
      simp_rw [influence_eq_sum_fourier]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S ⊆ J
      · -- S ⊆ J: LHS = 0
        rw [if_neg (not_not.mpr hS)]
        apply Finset.sum_nonneg
        intro i _
        by_cases hi : i ∈ S <;> simp [hi]; positivity
      · -- S ⊄ J
        rw [if_pos hS]
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hS
        have hi_mem : i ∈ Finset.univ.filter (fun i => i ∉ J) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩
        apply le_trans _ (Finset.single_le_sum (f := fun j => if j ∈ S then fourierCoeff f S ^ 2 else 0)
          (fun j _ => by by_cases hj : j ∈ S <;> simp [hj]; positivity) hi_mem)
        simp [hiS]
    -- Step 4: ∑_{i∉J} Inf_i < n * τ
    have hinfluence : ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f ≤ n * τ := by
      calc ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => i ∉ J), τ := by
            apply Finset.sum_le_sum; intro i hi
            have hni : i ∉ J := (Finset.mem_filter.mp hi).2
            simp only [J, influentialCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hni
            linarith [lt_of_not_ge hni]
        _ ≤ n * τ := by
            rw [Finset.sum_const, nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hτ)
            have : (Finset.univ.filter (fun i => i ∉ J)).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_filter_le _ _
            simp at this
            exact_mod_cast this
    linarith [hbound, hunion, hinfluence]
