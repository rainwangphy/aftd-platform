import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProdFinsetEqProdUnivIte
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# ArrowTheorem.profile_kernel_gen

Topic: social_choice   Node: 1dbe0d1a903f

Provenance: helper lemma. TCSlib, `ArrowTheorem.profile_kernel_gen`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

General profile kernel for paired preference assignments. Let $x, y : \mathrm{Fin}\,6 \to \mathrm{Bool}$ be two preference assignments whose sign
encodings have balanced marginals, $\sum_{k=1}^{6}\sigma(x_k) =
\sum_{k=1}^{6}\sigma(y_k) = 0$, and whose signed correlation is
$\sum_{k=1}^{6}\sigma(x_k)\,\sigma(y_k) = -2$. For a profile $p : \mathrm{Fin}\,n \to
\mathrm{Fin}\,6$, write $x\circ p$ and $y\circ p$ for the points of the Boolean
hypercube whose $i$-th coordinates are $x_{p(i)}$ and $y_{p(i)}$. Then for all subsets
$S, T \subseteq [n]$, the average of the product of Walsh characters over all $6^n$
profiles satisfies
\[
  \Bigl(\tfrac16\Bigr)^{n}\sum_{p:\mathrm{Fin}\,n \to \mathrm{Fin}\,6}
    \chi_S(x\circ p)\,\chi_T(y\circ p)
  \;=\;
  \begin{cases} \bigl(-\tfrac13\bigr)^{\abs{S}} & S = T,\\[2pt] 0 & S \ne T. \end{cases}
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- General kernel: any preference pair with zero marginals and cross-sum -2. -/
lemma ArrowTheorem.profile_kernel_gen {xPref yPref : Fin 6 → Bool}
    (hx : ∑ k : Fin 6, boolToSign (xPref k) = 0)
    (hy : ∑ k : Fin 6, boolToSign (yPref k) = 0)
    (hxy : ∑ k : Fin 6, boolToSign (xPref k) * boolToSign (yPref k) = -2)
    (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (fun i => xPref (p i)) * chiS T (fun i => yPref (p i)) =
    if S = T then (-1/3 : ℝ)^S.card else 0 := by
  simp only [chiS]
  simp_rw [prod_finset_eq_prod_univ_ite S, prod_finset_eq_prod_univ_ite T,
           ← Finset.prod_mul_distrib]
  rw [show ∑ p : Profile n, ∏ i : Fin n,
        ((if i ∈ S then boolToSign (xPref (p i)) else 1) *
         (if i ∈ T then boolToSign (yPref (p i)) else 1)) =
        ∏ i : Fin n, ∑ k : Fin 6,
        ((if i ∈ S then boolToSign (xPref k) else 1) *
         (if i ∈ T then boolToSign (yPref k) else 1)) from
    (Fintype.prod_sum (fun i (k : Fin 6) =>
       (if i ∈ S then boolToSign (xPref k) else 1) *
       (if i ∈ T then boolToSign (yPref k) else 1))).symm]
  have per_voter : ∀ i : Fin n,
      ∑ k : Fin 6, (if i ∈ S then boolToSign (xPref k) else 1) *
                   (if i ∈ T then boolToSign (yPref k) else 1) =
      if i ∈ S then (if i ∈ T then (-2 : ℝ) else 0) else (if i ∈ T then 0 else 6) := by
    intro i
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · simp only [if_pos hiS, if_pos hiT]; exact hxy
    · simp only [if_pos hiS, if_neg hiT, mul_one]; simpa using hx
    · simp only [if_neg hiS, if_pos hiT, one_mul]; simpa using hy
    · simp only [if_neg hiS, if_neg hiT, mul_one]; norm_num [Fin.sum_univ_six]
  simp_rw [per_voter]
  by_cases hST : S = T
  · subst hST
    simp only [if_true]
    simp_rw [show ∀ i : Fin n,
        (if i ∈ S then (if i ∈ S then (-2:ℝ) else 0) else (if i ∈ S then 0 else 6)) =
        if i ∈ S then (-2:ℝ) else 6 from fun i => by by_cases hi : i ∈ S <;> simp [hi]]
    simp_rw [show ∀ i : Fin n,
        (if i ∈ S then (-2:ℝ) else 6) = 6 * (if i ∈ S then (-1/3:ℝ) else 1) from
      fun i => by by_cases hi : i ∈ S; simp [hi]; norm_num; simp [hi]]
    rw [Finset.prod_mul_distrib]
    have h6 : ∏ _i : Fin n, (6 : ℝ) = 6 ^ n := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have prod_ite : ∏ i : Fin n, (if i ∈ S then (-1/3 : ℝ) else 1) = (-1/3 : ℝ) ^ S.card := by
      rw [← Finset.prod_filter, show Finset.univ.filter (· ∈ S) = S from by simp,
          Finset.prod_const]
    rw [h6, prod_ite]
    rw [← mul_assoc, ← mul_pow, show (1/6 : ℝ) * 6 = 1 from by norm_num, one_pow, one_mul]
  · simp only [if_neg hST]
    have hne : symmDiff S T ≠ ∅ := by
      intro h
      apply hST
      have : symmDiff S T = ⊥ := by rwa [Finset.bot_eq_empty]
      exact symmDiff_eq_bot.mp this
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [Finset.mem_symmDiff] at hi
    rw [mul_eq_zero]
    right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · simp only [if_pos hiS, if_neg hiT]
    · simp only [if_neg hiS, if_pos hiT]
