import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordExistenceBound
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordWeight

/-!
# ErrorCorrectingCodes.Codeword.gv_bound

Topic: information   Node: bf3b69b982ac

Provenance: formalization of a published result. Source: Gilbert–Varshamov bound for linear codes, as formalized in TCSlib (`ErrorCorrectingCodes.Codeword.gv_bound`). Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/GilbertVarshamov.lean (Apache-2.0); 1 adapted; compiled here.

Gilbert–Varshamov bound for linear codes. Let $\alpha$ be a finite field with $q = \abs{\alpha}$ elements, and let $n, k, d$ be
natural numbers. Write $B_{d-1}(\mathbf{0})$ for the Hamming ball of radius $d-1$ about
the all-zero codeword in $\alpha^n$, and suppose
\[
k \le n - \bigl\lceil \log_q \abs{B_{d-1}(\mathbf{0})} \bigr\rceil - 1.
\]
Then there exists an $n \times k$ generator matrix $G$ over $\alpha$ such that for every
nonzero message $x \in \alpha^k$, the codeword $Gx \in \alpha^n$ has Hamming weight at
least $d$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Gilbert–Varshamov bound**: if `k ≤ n − ⌈log_q Vol(n, d−1)⌉ − 1`, then there exists an `n×k` generator matrix `G` such that every nonzero message is mapped to a codeword of Hamming weight at least `d`. -/
theorem ErrorCorrectingCodes.Codeword.gv_bound (n k q d : ℕ) (h_q : q = (Fintype.card α)) (h_k : k ≤ n - ((Nat.clog q) (hamming_ball (d-1) (zero : Codeword n α)).card) - 1):
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∀ (x : Codeword k α), x ≠ 0 → weight (Matrix.mulVec G x) ≥ d}).card ≥ 1 := by {
  set bc := (hamming_ball (d-1) (zero : Codeword n α)).card with h_bc_def
  let bad_G := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), x ≠ 0 ∧ weight (Matrix.mulVec G x) < d}
  have h_good_eq : Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∀ (x : Codeword k α), x ≠ 0 → weight (Matrix.mulVec G x) ≥ d} =
      Finset.univ \ bad_G := by
    ext G
    simp only [bad_G, Finset.mem_sdiff, Finset.mem_univ, true_and,
               Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · intro h ⟨x, hxne, hlt⟩; exact absurd (h x hxne) (Nat.not_le.mpr hlt)
    · intro h x hxne; exact Nat.le_of_not_lt (fun hlt => h ⟨x, hxne, hlt⟩)
  have h_all_card : Fintype.card (Matrix (Fin n) (Fin k) α) = (Fintype.card α)^(n*k) := by
    rw [show Fintype.card (Matrix (Fin n) (Fin k) α) = Fintype.card (Fin n → Fin k → α) from
      Fintype.card_congr (Equiv.refl _)]
    simp only [Fintype.card_fun, Fintype.card_fin]; ring
  have hq_gt1 : 1 < (Fintype.card α) := Fintype.one_lt_card
  have hq_gt1' : 1 < q := h_q ▸ hq_gt1
  have hq_pos : 0 < (Fintype.card α) := by omega
  have h_ball_le_pow_of_clog_le : ∀ c : ℕ, Nat.clog q bc ≤ c → bc ≤ (Fintype.card α)^c := by
    intro c hc
    rw [h_bc_def, ← h_q] at *
    exact (Nat.clog_le_iff_le_pow hq_gt1').mp hc
  rw [h_good_eq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h_all_card]
  suffices h : bad_G.card < (Fintype.card α)^(n*k) by omega
  by_cases hk0 : k = 0
  · have h_bad_empty : bad_G = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      simp only [bad_G, Set.mem_toFinset, Set.mem_setOf_eq, not_exists, not_and]
      intro G x hxne
      have : x = 0 := by ext i; exact Fin.elim0 (hk0 ▸ i)
      exact absurd this hxne
    simp [h_bad_empty, hk0]
  · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk0
    have h_clog_le : Nat.clog q bc + k + 1 ≤ n := by omega
    have h_ball_le_pow : bc ≤ (Fintype.card α)^(n - k - 1) :=
      h_ball_le_pow_of_clog_le _ (by omega)
    by_cases hd0 : d = 0
    · have h_bad_empty : bad_G = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        simp only [bad_G, Set.mem_toFinset, Set.mem_setOf_eq, not_exists, not_and]
        intro G x _; simp [hd0]
      simp [h_bad_empty]; positivity
    · have hd_pos : d > 0 := Nat.pos_of_ne_zero hd0
      have h_exist : bad_G.card ≤
          ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * bc :=
        existence_bound d hk_pos hd_pos
      have hn_pos : 1 ≤ n := by omega
      have hnk_ge_n : n ≤ n * k := Nat.le_mul_of_pos_right n hk_pos
      have hnk_ge_k : k ≤ n * k := Nat.le_mul_of_pos_left k hn_pos
      have h_exp_combine : n*k - n + (n - k - 1) = n*k - k - 1 := by omega
      have h_exp_merge : k + (n*k - k - 1) = n*k - 1 := by omega
      have h_combine : ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) *
          (Fintype.card α)^(n - k - 1) = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - k - 1) := by
        rw [mul_assoc, ← pow_add, h_exp_combine]
      calc bad_G.card
          ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * bc := h_exist
        _ ≤ ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - n) * (Fintype.card α)^(n - k - 1) :=
            Nat.mul_le_mul_left _ h_ball_le_pow
        _ = ((Fintype.card α)^k - 1) * (Fintype.card α)^(n*k - k - 1) := h_combine
        _ < (Fintype.card α)^k * (Fintype.card α)^(n*k - k - 1) :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.sub_lt (Nat.pow_pos hq_pos) Nat.one_pos)
              (Nat.pow_pos hq_pos)
        _ = (Fintype.card α)^(n*k - 1) := by rw [← pow_add, h_exp_merge]
        _ ≤ (Fintype.card α)^(n*k) := Nat.pow_le_pow_right hq_pos (by omega)
}
