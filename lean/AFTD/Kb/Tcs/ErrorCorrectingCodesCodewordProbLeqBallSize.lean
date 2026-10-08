import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordWeight
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordMatrixDist
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordUniformVectorDist
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordUniformityLemma
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.Weight

/-!
# ErrorCorrectingCodes.Codeword.prob_leq_ball_size

Topic: information   Node: 22a368052ab5

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.prob_leq_ball_size`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/GilbertVarshamov.lean (Apache-2.0); 1 adapted; compiled here.

Weight distribution of a random linear image is dominated by a Hamming ball. Let $\alpha$ be a finite field, let $n$ and $k \ge 1$ be natural numbers, and fix a
nonzero codeword $x \in \alpha^{k}$ together with an integer $d > 0$. Regard an $n
\times k$ matrix $G$ over $\alpha$ as chosen uniformly at random among all
$\abs{\alpha}^{nk}$ such matrices, so that the image $Gx$ is a codeword of length $n$.
Then the probability that $Gx$ has Hamming weight strictly less than $d$ is at most the
fraction of all codewords of length $n$ that lie in the Hamming ball of radius $d-1$
about the all-zero codeword:
\[
\frac{\abs{\{\, G \in \alpha^{n \times k} : \operatorname{wt}(Gx) < d
\,\}}}{\abs{\alpha}^{nk}}
\;\le\;
\frac{\abs{B_{d-1}(\mathbf{0})}}{\abs{\alpha}^{n}}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Probabilistic bound**: for any nonzero message `x ∈ αᵏ`, the fraction of `n×k` matrices `G` for which `G·x` has Hamming weight less than `d` is at most `Vol(n,d−1)/|α|ⁿ`. -/
theorem ErrorCorrectingCodes.Codeword.prob_leq_ball_size (x : Codeword k α) (d : ℕ) (h_k : k ≥ 1) (h_x : x ≠ 0) (h_d : d > 0) :
((Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) / (Fintype.card α : ℝ)^(n*k) ≤
((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n := by {

  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}
  let S' := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) ∈ hamming_ball (d-1) zero}

  have h_card_eq : S.card = S'.card := by
    let f : (G : Matrix (Fin n) (Fin k) α) → G ∈ S → (Matrix (Fin n) (Fin k) α) := fun G _ ↦ G
    apply Finset.card_bij f

    have h_map : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), f G hG ∈ S' := by
      simp only [toFinset_setOf, mem_filter, Finset.mem_univ, true_and, S, f]
      unfold weight
      intro G h_dist_le_d
      have h_dist_leq_dminus1 : hamming_distance (Matrix.mulVec G x) zero ≤ d - 1 := by
        have h₁ : (hamming_distance (Matrix.mulVec G x) zero) + 1 ≤ d := by exact Nat.succ_le_of_lt h_dist_le_d
        have h₂ : (hamming_distance (Matrix.mulVec G x) zero) + 1 - 1 ≤ d - 1 := by exact Nat.sub_le_sub_right h₁ 1
        rw[Nat.add_sub_cancel] at h₂
        exact h₂
      rw [mem_toFinset]
      simp[h_dist_leq_dminus1]

    exact h_map

    have h_inj : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), ∀ (G' : Matrix (Fin n) (Fin k) α) (hG' : G' ∈ S), f G hG = f G' hG' → G = G' := by
      intro G G' hG hG' h_fG_eq
      simp[h_fG_eq, f, S]

    exact h_inj

    have h_surj : ∀ G' ∈ S', ∃ G, ∃ (hG : G ∈ S), f G hG = G' := by
      intro G' h_G'inS'
      use G'
      simp only [toFinset_setOf, mem_filter, Finset.mem_univ, true_and, exists_prop, and_true, f, S]
      try simp at h_G'inS'
      rw[mem_toFinset] at h_G'inS'
      simp only [hamming_ball, toFinset_setOf, mem_filter, Finset.mem_univ, true_and,
        mem_setOf_eq] at h_G'inS'
      unfold weight
      apply Nat.lt_of_le_pred
      simp only [h_d]
      exact h_G'inS'
    exact h_surj

  simp only [toFinset_setOf, hamming_ball, mem_filter, Finset.mem_univ, true_and, S,
    S'] at h_card_eq
  simp only [toFinset_setOf, hamming_ball, ge_iff_le]
  rw[h_card_eq]

  let matrix_uniformity := uniformity_lemma n k x h_x h_k

  unfold matrix_dist uniform_vector_dist at matrix_uniformity
  simp only [Finite.toFinset_setOf, one_div] at matrix_uniformity

  have h_unif (v: Codeword n α) : (toFinset {G | Matrix.mulVec G x = v}).card / Fintype.card α ^ (n * k) = 1 / ((Fintype.card α : ℝ))^n := by
    apply congr_fun at matrix_uniformity
    specialize matrix_uniformity v
    have h_filter_eq : ↑(filter (fun x_1 => Matrix.mulVec x_1 x = v) Finset.univ) = (toFinset {G | Matrix.mulVec G x = v}) := by
      ext y
      constructor
      · intro h_filter
        rw[Finset.mem_filter] at h_filter
        simp_rw[Set.mem_toFinset, Set.mem_setOf, h_filter]
      · intro h_finset
        rw[Set.mem_toFinset, Set.mem_setOf] at h_finset
        rw[Finset.mem_filter]
        simp[h_finset]

    rw[←h_filter_eq]
    have h_inv : ((Fintype.card α : ℝ) ^ n)⁻¹ = 1 / (Fintype.card α : ℕ) ^ n := by
      rw [one_div]
    rw_mod_cast[←h_inv]
    exact matrix_uniformity

  have h_sum : ((toFinset {G : (Matrix (Fin n) (Fin k) α) | Matrix.mulVec G x ∈ hamming_ball (d - 1) zero}).card : ℝ) / (Fintype.card α : ℝ) ^ (n * k) = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => 1 / (Fintype.card α : ℝ)^n := by
    simp only [hamming_ball, toFinset_setOf, mem_filter, Finset.mem_univ, true_and, one_div,
      sum_const, nsmul_eq_mul]
    have h_ball_eq_sum : (toFinset {G | Matrix.mulVec G x ∈ hamming_ball (d-1) zero}) = (Set.toFinset (⋃ (v : Fin n → α) (h_v : weight v ≤ d-1), {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) = v})) := by
      simp only [hamming_ball, toFinset_setOf, mem_filter, Finset.mem_univ, true_and]
      ext y
      constructor
      · intro h_ball
        simp only [mem_toFinset, mem_iUnion, mem_setOf_eq, exists_prop, exists_eq_right']
        simp only [mem_filter, Finset.mem_univ, true_and] at h_ball
        unfold weight
        simp[h_ball]
      · intro h_union
        apply Set.mem_toFinset.mp at h_union
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h_union
        obtain ⟨hwt, hG⟩ := Set.mem_iUnion.mp hv
        have h_yxv : Matrix.mulVec y x = v := hG
        have h_yx_hd : hamming_distance (Matrix.mulVec y x) 0 ≤ d - 1 := by rw[h_yxv]; exact hwt
        have h_yx_set : Matrix.mulVec y x ∈ toFinset {c' | hamming_distance c' 0 ≤ d - 1} := Set.mem_toFinset.mpr h_yx_hd
        exact (mem_filter_univ y).mpr h_yx_hd

    unfold hamming_ball at h_ball_eq_sum
    simp only [toFinset_setOf, mem_filter, Finset.mem_univ, true_and] at h_ball_eq_sum
    rw[h_ball_eq_sum]

    have h_card_eq_sum : (toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v})).card = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => (toFinset {G | Matrix.mulVec G x = v}).card := by
      let hamming_set : Finset (Codeword n α) := toFinset {v | hamming_distance v zero ≤ d - 1}
      let f : Codeword n α → Finset (Matrix (Fin n) (Fin k) α) := fun v => toFinset {G | Matrix.mulVec G x = v}
      let G_union : Finset (Matrix (Fin n) (Fin k) α) := hamming_set.biUnion f

      have h_G_union : G_union = toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v}) := by
        ext G
        simp [Set.mem_toFinset, Set.mem_setOf_eq]
        constructor
        · intro h_a
          simp[G_union] at h_a
          let ⟨a, h_adist, h_Ga⟩ := h_a
          rw[Set.mem_toFinset, Set.mem_setOf] at h_Ga
          rw[←h_Ga] at h_adist
          unfold weight
          simp[hamming_set] at h_adist
          exact h_adist
        · intro h_weight
          let a := Matrix.mulVec G x
          simp[G_union]
          use a
          apply And.intro
          · simp[hamming_set]; exact h_weight
          · rw[Set.mem_toFinset, Set.mem_setOf]

      have h_disjoint : ∀ x ∈ hamming_set, ∀ y ∈ hamming_set, x ≠ y → Disjoint (f x) (f y) := by
        intro a h_a b h_b h_ab
        simp[f]
        rw[Finset.disjoint_iff_ne]
        intro G h_Ga H h_Ha
        simp at h_Ga h_Ha
        rw [←h_Ga, ←h_Ha] at h_ab
        by_contra h_GHeq
        have h_mul_eq : Matrix.mulVec G x = Matrix.mulVec H x := by simp[h_GHeq]
        contradiction

      rw[←h_G_union]
      apply Finset.card_biUnion h_disjoint

    rw[h_card_eq_sum]
    field_simp[matrix_uniformity]
    have h_preimage_card : ∀ (v : Codeword n α), ((toFinset {G | Matrix.mulVec G x = v}).card : ℝ) = ↑(Fintype.card α) ^ (n * k - n) := by
      intro v₀
      specialize h_unif v₀
      field_simp at h_unif
      have h_card_exp : ↑(toFinset {G | Matrix.mulVec G x = v₀}).card  = ((Fintype.card α : ℝ) ^ (n * k)) / ((Fintype.card α : ℝ) ^ n) := by field_simp; exact h_unif
      rw[h_card_exp]
      field_simp[h_card_exp]
      norm_cast
      simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k := by
        rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k'
      have : n + (n * k - n) = n * k := by linarith[h_pow_eq]
      rw[this]

    simp at h_preimage_card
    simp
    simp_rw[h_preimage_card, Finset.sum_const, nsmul_eq_mul]

    have h_exp : (Fintype.card α : ℝ)^(n * k - n) * (Fintype.card α : ℝ)^n = (Fintype.card α : ℝ)^(n * k) := by
      simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k := by
        rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k'
      rw[h_pow_eq]

    rw[←h_exp]
    simp[mul_assoc]
    linarith


  have h_ball_size : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = ((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n := by
    have h_sum_mult : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}).card * (1 / (Fintype.card α : ℝ)^n) := by simp[Finset.sum_const]
    rw[h_sum_mult]
    field_simp
    simp
  simp at h_sum
  simp at h_ball_size
  rw[h_sum, h_ball_size]
}
