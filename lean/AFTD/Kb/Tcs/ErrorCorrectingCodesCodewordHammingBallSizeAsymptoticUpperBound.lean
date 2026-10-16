import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordLtOneOfLeOneSubInv
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastSubOnePosOfTwoLe
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordOneSubPosOfLtOne
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordQaryEntropy
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBallSize
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero

/-!
# ErrorCorrectingCodes.Codeword.hamming_ball_size_asymptotic_upper_bound

Topic: information   Node: 930fc75f2e3b

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.hamming_ball_size_asymptotic_upper_bound`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Entropy.lean (Apache-2.0); 1 adapted; compiled here.

Entropy upper bound on Hamming balls. Let $\alpha$ be a finite alphabet with at least two symbols, write $q = \abs{\alpha}$
for its size, and let $n$ be a natural number. Fix a real number $p$ with $0 < p \le 1 -
1/q$, and let
\[
H_q(p) \;=\; p\log_q(q-1) - p\log_q p - (1-p)\log_q(1-p)
\]
be the $q$-ary entropy function. Then for every codeword $c \in \alpha^n$, the Hamming
ball of radius $\lfloor np\rfloor$ about $c$, namely $B_{\lfloor np\rfloor}(c) = \{c'
\in \alpha^n : d(c',c) \le \lfloor np\rfloor\}$, satisfies
\[
\abs{B_{\lfloor np\rfloor}(c)} \;\le\; q^{\,H_q(p)\,n}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ErrorCorrectingCodes ErrorCorrectingCodes.Codeword in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
variable {x : ℝ} in
/-- **Asymptotic upper bound on ball size**: for `0 < p ≤ 1 - 1/q`, the Hamming ball of radius `⌊np⌋` has at most `q^(H_q(p)·n)` elements. -/
theorem ErrorCorrectingCodes.Codeword.hamming_ball_size_asymptotic_upper_bound (q n : ℕ) (p : ℝ)
    (hq : q = Fintype.card α) (hα : Nontrivial α)
    (hp : 0 < p ∧ p ≤ 1 - 1/q) :
    ∀ c : Codeword n α,
      (hamming_ball (Nat.floor (n*p)) c).card ≤ Real.rpow q ((qaryEntropy q p) * n) := by {
  intro c
  rw[hamming_ball_size]
  rw[← hq]
  have hq_pos : (0 : ℝ) < q := by
    rw [hq, Nat.cast_pos]
    exact Fintype.card_pos
  have hq_sub_one_nonneg : (0 : ℝ) ≤ ↑q - 1 := by
    rw [sub_nonneg]
    have : (1 : ℝ) ≤ q := by
      rw [hq]
      exact_mod_cast Nat.one_le_of_lt Fintype.card_pos
    exact this
  have hq_sub_one_pos : (0 : ℝ) < ↑q - 1 := by
    rw [hq]
    exact natCast_sub_one_pos_of_two_le (Nat.succ_le_iff.mpr Fintype.one_lt_card)
  have hp_lt_one : p < 1 := lt_one_of_le_one_sub_inv hq_pos hp.2
  have h_one_sub_p : 0 < 1 - p := one_sub_pos_of_lt_one hp_lt_one
  apply (div_le_one (by simpa using Real.rpow_pos_of_pos hq_pos ((qaryEntropy q p) * n))).1
  simp
  dsimp[qaryEntropy]

  rw[div_eq_mul_inv, ← Real.rpow_neg]
  have : -((p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p)) * ↑n) =
          (Real.logb (↑q) (↑q - 1)) * (-p * ↑n) + (Real.logb (↑q) p) * (p * ↑n) + (Real.logb (↑q) (1 - p)) * ((1-p) * ↑n) := by linarith
  rw[this]

  rw[Real.rpow_add, Real.rpow_add, Real.rpow_mul, Real.rpow_logb, Real.rpow_mul, Real.rpow_mul, Real.rpow_mul,Real.rpow_mul]
  rw[Real.rpow_logb, Real.rpow_logb]
  rw[← Real.rpow_mul, ← Real.rpow_mul]
  rw[Finset.sum_mul]


  simp only [neg_mul, ge_iff_le]

-- Doing all the algebra
  have h_alg1 : ∀ x, ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n)) =
  ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n) := by
    intro x
    rw[one_sub_mul, sub_eq_add_neg ↑n (p * ↑n)]
    rw[Real.rpow_add h_one_sub_p, ← mul_assoc, ← Real.rpow_natCast]
    calc
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x :ℝ) * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n)) * ((1 - p) ^ (n : ℝ) * (1 - p) ^ (-(p * ↑n))) =
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * ((((1 - p) ^(-(p * ↑n)) * (↑q - 1) ^ (-(p * ↑n)))) * p ^ (p * ↑n)) := by linarith
      _ = ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by {
        rw[← Real.mul_rpow]
        rw[Real.rpow_neg, ← Real.inv_rpow]
        rw[← Real.mul_rpow]
        rw[← div_eq_inv_mul]
        ring_nf
        · apply inv_nonneg.2
          apply mul_nonneg
          exact le_of_lt h_one_sub_p
          exact hq_sub_one_nonneg
        · linarith
        · exact (mul_nonneg_iff_of_pos_left h_one_sub_p).mpr hq_sub_one_nonneg
        · exact (mul_nonneg_iff_of_pos_left h_one_sub_p).mpr hq_sub_one_nonneg
        · exact le_of_lt h_one_sub_p
        · exact hq_sub_one_nonneg
      }

  have h_alg_2 : ∀ x ∈ (Finset.range (⌊↑n * p⌋₊ + 1)), ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x) := by
    intros x hx
    suffices (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (p / ((↑q - 1) * (1 - p))) ^ x by {
      calc
        ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) =
        (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ)) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by linarith
        _ ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x) := by rel[this]
    }
    simp only [Finset.mem_range] at hx
    have : 0 < (p / ((↑q - 1) * (1 - p))) ∧ (p / ((↑q - 1) * (1 - p))) ≤ 1 := by
      constructor
      · apply div_pos
        linarith[hp.1]
        apply mul_pos
        exact hq_sub_one_pos
        linarith[h_one_sub_p]
      · suffices p / (q - 1) ≤ 1 - p by {
          rw[← div_div]
          apply (div_le_one h_one_sub_p).2
          exact this
        }
        calc
          p / (↑q - 1) ≤ 1/q := by {
            apply (div_le_iff₀ hq_sub_one_pos).2
            rw[mul_sub, one_div, mul_one, inv_mul_cancel₀]
            rw [one_div] at hp
            exact hp.2
            exact ne_of_gt hq_pos
          }
          _ ≤ 1 - p := by linarith

    have h_x_le_pn : x ≤ p * n := by
      have : 0 ≤ n*p := by
        apply mul_nonneg
        exact Nat.cast_nonneg n
        linarith[hp.1]
      rw[mul_comm]
      apply (Nat.le_floor_iff this).1
      exact Nat.lt_succ.mp hx

    rw[← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge this.1 this.2 h_x_le_pn



  calc
      (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n))) =  (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n)) := by {
      apply Finset.sum_congr
      rfl
      intro x hx
      exact h_alg1 x
    }
    _ ≤ (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum
      intros i hi
      exact h_alg_2 i hi
    }
    _ ≤ (Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg

      apply range_subset.2
      simp only [Finset.mem_range]
      intro x hx
      apply lt_of_lt_of_le hx
      simp only [add_le_add_iff_right]
      apply Nat.floor_le_of_le
      calc
        ↑n * p ≤ ↑n * 1 := by exact mul_le_mul_of_nonneg_left (le_of_lt hp_lt_one) (Nat.cast_nonneg n)
        _      ≤ ↑n     := by simp
      intros i _ _
      repeat apply mul_nonneg
      simp only [Nat.cast_nonneg]
      simp only [Nat.cast_nonneg, pow_nonneg]
      simp only [Real.rpow_natCast]
      exact pow_nonneg (le_of_lt h_one_sub_p) n
      apply pow_nonneg
      apply div_nonneg
      exact le_of_lt hp.1
      apply mul_nonneg
      exact hq_sub_one_nonneg
      exact le_of_lt h_one_sub_p
    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * p ^ x * (1 - p) ^ ((n : ℝ) - x)) := by{
      apply Finset.sum_congr
      rfl
      intros x hx
      simp at hx
      try apply Nat.lt_succ.1 at hx
      rw[div_pow, mul_pow]
      field_simp
      simp
      symm
      calc
        ↑(Nat.choose n x) * p ^ x * (↑q - 1) ^ x * (1 - p) ^ x * (1 - p) ^ ((n:ℝ) - (x:ℝ)) =
        ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ ((n:ℝ) - (x:ℝ)) * (1 - p) ^ x) * p ^ x := by linarith
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ (n - x) * (1 - p) ^ x) * p ^ x := by rw[←Nat.cast_sub hx, Real.rpow_natCast]
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * (1 - p) ^ n * p ^ x := by rw[←pow_add, Nat.sub_add_cancel hx]
        _ = ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ n * p ^ x := by {
          simp only [mul_eq_mul_right_iff, mul_eq_mul_left_iff, Nat.cast_eq_zero, pow_eq_zero_iff',
            ne_eq]
          left
          left
          left
          rw[Nat.cast_sub, Nat.cast_one]
          rw[hq]
          exact Nat.one_le_of_lt Fintype.card_pos
        }
    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (p ^ x * (1 - p) ^ (n - x) * ↑(Nat.choose n x)) := by {
      apply Finset.sum_congr
      rfl
      intros x hx
      simp only [Finset.mem_range] at hx
      apply Nat.lt_succ.1 at hx
      rw[←Nat.cast_sub hx, Real.rpow_natCast]
      linarith
    }
    _ = 1 := by {
      rw[← add_pow p (1-p) n]
      simp only [add_sub_cancel, one_pow]
    }

  -- More algebras on inequalities
  exact le_of_lt hp.1
  exact hq_sub_one_nonneg
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact h_one_sub_p
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hp.1
  exact le_of_lt hq_pos
  rw[Real.rpow_logb]
  exact le_of_lt hp.1
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hp.1
  linarith[hq_pos]
  exact hq_sub_one_nonneg
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hq_sub_one_pos
  linarith[hq_pos]
  exact hq_pos
  exact hq_pos
  linarith[hq_pos]
}
