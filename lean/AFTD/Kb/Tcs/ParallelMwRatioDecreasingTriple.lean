import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwBalancingBasePolynomial
import AFTD.Kb.Tcs.ParallelMwBalancingTransferBound
import AFTD.Kb.Tcs.ParallelMwBalancingNumeratorBound
import AFTD.Kb.Tcs.ParallelMwBalancingStrictCore
import AFTD.Kb.Tcs.ParallelMwTwoPowQuadraticBound

/-!
# parallel_mw_ratio_decreasing_triple

Topic: combinatorics   Node: 969372bb8eec

Provenance: helper lemma. step towards parallel_uniform_merino_welsh_strict_balancing_three_two

For positive integers a, b, c with a + 2 ≤ b, replacing (a, b) with (a + 1, b - 1) strictly decreases the rational formula for parallel_mw_ratio 2.
-/

/-- Strict decrease of the 3-variable Merino-Welsh ratio formula under transferring weight from a larger coordinate to a smaller coordinate. -/
theorem parallel_mw_ratio_decreasing_triple (a b c : ℕ) (ha : 0 < a) (hij : a + 2 ≤ b) (hc : 0 < c) :
    6 * ((2 : ℝ) ^ (a + b + c) - 2 * ((2 : ℝ) ^ (a + 1) + (2 : ℝ) ^ (b - 1) + (2 : ℝ) ^ c) + 6) /
      (((a + 1 : ℝ) * (b - 1) + (a + 1 : ℝ) * c + (b - 1 : ℝ) * c) ^ 2) <
    6 * ((2 : ℝ) ^ (a + b + c) - 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ b + (2 : ℝ) ^ c) + 6) /
      (((a : ℝ) * b + (a : ℝ) * c + (b : ℝ) * c) ^ 2) := by
  set_option maxHeartbeats 1000000 in
    let d : ℕ := b-a-1
    have hd : 1 ≤ d := by dsimp [d]; omega
    have hb : b = a+d+1 := by dsimp [d]; omega
    have hbm : b-1 = a+d := by dsimp [d]; omega
    let A : ℝ := 2^a
    let B : ℝ := 2^(b-1)
    let C : ℝ := 2^c
    let s : ℝ := (a : ℝ)+c
    let t : ℝ := (a : ℝ)*((a : ℝ)+1)+(2*(a : ℝ)+1)*(c : ℝ)
    let u : ℝ := s*d+t
    let N : ℝ := 2*A*B*C-2*A-4*B-2*C+6
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hApos : 0 < A := by dsimp [A]; positivity
    have hlin (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
      have hn : k+1 ≤ 2^k := Nat.succ_le_iff.mpr k.lt_two_pow_self
      exact_mod_cast hn
    have hA : (a : ℝ)+1 ≤ A := hlin a
    have hC : (c : ℝ)+1 ≤ C := hlin c
    have hquad : (a : ℝ)^2+a ≤ 2*A := parallel_mw_two_pow_quadratic_bound a
    have hBfactor : B=A*(2:ℝ)^d := by dsimp [A,B]; rw [hbm,pow_add]
    have hdPow : (2:ℝ) ≤ 2^d := by
      have hn : (2 : ℕ) ≤ 2^d := by
        calc 2=2^1 := by norm_num
          _ ≤ 2^d := Nat.pow_le_pow_right (by norm_num) hd
      exact_mod_cast hn
    have hB : 2*A ≤ B := by rw [hBfactor]; nlinarith
    have hgap : (a : ℝ) = 1 ∨ 2 ≤ (a : ℝ) := by
      have hNat : a = 1 ∨ 2 ≤ a := by omega
      rcases hNat with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hsmall : (a : ℝ)=1 → A=2 := by
      intro h
      have : a=1 := by exact_mod_cast h
      subst a
      norm_num [A]
    have hbound0 := parallel_mw_balancing_numerator_bound (a:ℝ) (c:ℝ) A B C ha' hc' hA hC hquad hgap hsmall hB
    have hs : 0 < s := by dsimp [s]; positivity
    have ht : 2*s ≤ t := by
      dsimp [s,t]
      have h1 := mul_nonneg (show 0 ≤ (a : ℝ)-1 by linarith) (show 0 ≤ (a : ℝ) by positivity)
      have h2 := mul_nonneg (show 0 ≤ 2*(a : ℝ)-1 by linarith) (show 0 ≤ (c : ℝ) by positivity)
      nlinarith
    have hst : s+t = (a:ℝ)*((a:ℝ)+2)+2*((a:ℝ)+1)*(c:ℝ) := by dsimp [s,t]; ring
    have hbound : B*(s+t) ≤ 2*N := by dsimp [N]; rw [hst]; exact hbound0
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hN : 0 < N := by
      have htpos : 0 < t := by linarith
      have hh : 0 < B*(s+t) := by positivity
      linarith
    have hcases : ((d:ℝ)=1 ∧ B=2*A) ∨ ((d:ℝ)=2 ∧ B=4*A) ∨
        ((d:ℝ)=3 ∧ B=8*A) ∨ 4 ≤ (d:ℝ) := by
      by_cases hh : d ≤ 3
      · interval_cases d
        · left; constructor <;> norm_num [hBfactor, mul_comm]
        · right; left; constructor <;> norm_num [hBfactor, mul_comm]
        · right; right; left; constructor <;> norm_num [hBfactor, mul_comm]
      · right; right; right; exact_mod_cast (show 4 ≤ d by omega)
    have hcore := parallel_mw_balancing_strict_core s t A B (d:ℝ) N hs ht hApos.le (by linarith) (by linarith) hN hcases hbound
    have hdcast : (b:ℝ)=(a:ℝ)+(d:ℝ)+1 := by exact_mod_cast hb
    have hu : u=(a:ℝ)*b+(a:ℝ)*c+(b:ℝ)*c := by dsimp [u,s,t]; rw [hdcast]; ring
    have hnew : (a+1:ℝ)*(b-1)+(a+1:ℝ)*c+(b-1:ℝ)*c = u+d := by rw [hu,hdcast]; ring
    have hu_pos : 0 < u := by rw [hu]; positivity
    have hnew_pos : 0 < u+(d:ℝ) := by linarith
    have hbp : (2:ℝ)^b=2*B := by dsimp [B]; conv_lhs => rw [show b=(b-1)+1 by omega]; rw [pow_succ, mul_comm]
    have hap : (2:ℝ)^(a+1)=2*A := by dsimp [A]; rw [pow_succ, mul_comm]
    have hprod : (2:ℝ)^(a+b+c)=2*A*B*C := by
      dsimp [A,B,C]
      rw [show a+b+c=a+(b-1)+c+1 by omega, pow_succ, pow_add, pow_add]
      ring
    rw [div_lt_div_iff₀ (sq_pos_of_pos (by rw [hnew]; exact hnew_pos)) (sq_pos_of_pos (by rw [←hu]; exact hu_pos))]
    rw [hnew, ←hu, hprod, hbp, hap]
    change 2*(B-A)*u^2 < N*(2*u*(d:ℝ)+(d:ℝ)^2) at hcore
    dsimp [N] at hcore
    nlinarith only [hcore]
