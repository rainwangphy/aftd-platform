import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordWeight
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordProbLeqBallSize
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.Weight

/-!
# ErrorCorrectingCodes.Codeword.existence_bound

Topic: information   Node: 477d9574d5b3

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.existence_bound`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/GilbertVarshamov.lean (Apache-2.0); 1 verbatim; compiled here.

Existence bound via union bound. Let $\alpha$ be a finite nonempty field, let $n$ and $k$ be natural numbers with $k \ge
1$, and let $d$ be a positive integer. Regard an $n \times k$ matrix $G$ over $\alpha$
as a map sending a message $x \in \alpha^{k}$ to the length-$n$ codeword $Gx$. Then the
number of such matrices $G$ for which some nonzero message $x$ has $\mathrm{wt}(Gx) < d$
is at most
\[
(\abs{\alpha}^{k} - 1)\cdot \abs{\alpha}^{\,nk - n}\cdot \abs{B_{d-1}(\mathbf 0)},
\]
where $\mathrm{wt}$ denotes Hamming weight and $B_{d-1}(\mathbf 0)$ is the Hamming ball
of radius $d-1$ about the all-zero codeword of length $n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Union bound**: the number of `n×k` generator matrices `G` for which some nonzero message `x` is sent to a codeword of weight less than `d` is at most `(|α|ᵏ − 1) · |α|^(nk−n) · Vol(n, d−1)`. -/
theorem ErrorCorrectingCodes.Codeword.existence_bound (d: ℕ) (h_k : k ≥ 1) (h_d : d > 0) :
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}).card ≤
((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * ((hamming_ball (d-1) (zero : Codeword n α)).card) := by {

  let nonzero : Finset (Codeword k α) := Finset.univ.filter (· ≠ 0)
  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}

  have h_union_eq : S = nonzero.biUnion (fun x => Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}) := by
    ext G
    simp [S, nonzero]

  have h_union_bound : S.card ≤ Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card) := by
    rw [h_union_eq]
    exact Finset.card_biUnion_le

  have h_each_x : ∀ x ∈ nonzero, (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card ≤ (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
    intro x hx
    have h_x_ne : x ≠ 0 := by simpa [nonzero] using hx
    have h_prob : ((Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) / (Fintype.card α : ℝ)^(n*k) ≤
        ((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n :=
      prob_leq_ball_size x d h_k h_x_ne h_d
    have hq_nk_pos : (0 : ℝ) < (Fintype.card α : ℝ)^(n*k) := by positivity
    have hq_n_pos : (0 : ℝ) < (Fintype.card α : ℝ)^n := by positivity
    have h_nk_ge_n : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    rw [div_le_div_iff₀ hq_nk_pos hq_n_pos] at h_prob
    have h_qnk_split : (Fintype.card α : ℝ)^(n*k) = (Fintype.card α : ℝ)^n * (Fintype.card α : ℝ)^(n*k - n) := by
      rw [← pow_add, Nat.add_sub_cancel' h_nk_ge_n]
    rw [h_qnk_split, ← mul_assoc] at h_prob
    have h_real : (↑(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) ≤
        ↑((Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      have h_rearrange : (↑(hamming_ball (d - 1) (zero : Codeword n α)).card : ℝ) *
          (Fintype.card α : ℝ) ^ n * (Fintype.card α : ℝ) ^ (n * k - n) =
          (Fintype.card α : ℝ) ^ (n * k - n) * ↑(hamming_ball (d - 1) (zero : Codeword n α)).card *
          (Fintype.card α : ℝ) ^ n := by ring
      rw [h_rearrange] at h_prob
      exact le_of_mul_le_mul_right h_prob hq_n_pos
    exact_mod_cast h_real

  have h_sum_leq : Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card) ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
    calc Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card)
        ≤ Finset.sum nonzero (fun _ => (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) :=
          Finset.sum_le_sum h_each_x
      _ = nonzero.card * ((Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card) := by
          simp [Finset.sum_const]
      _ = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (hamming_ball (d-1) (zero : Codeword n α)).card := by
          have h_nonzero_card : nonzero.card = (Fintype.card α)^k - 1 := by
            have h_nonzero_eq : nonzero = Finset.univ \ {(0 : Codeword k α)} := by
              ext x; simp [nonzero]
            rw [h_nonzero_eq, Finset.card_sdiff_of_subset (by simp)]
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Finset.card_singleton]
          rw [h_nonzero_card]
          ring

  trans Finset.sum nonzero (fun x => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card)
  · exact h_union_bound
  · exact h_sum_leq
}
