import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordQaryEntropy
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordBinomRatioBound

/-!
# ErrorCorrectingCodes.Codeword.listDecoding_counting_ineq

Topic: information   Node: 165d7de84915

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.listDecoding_counting_ineq`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/ListDecoding.lean (Apache-2.0); 1 verbatim; compiled here.

Counting inequality for list decoding. Fix an integer alphabet size $q \ge 2$, a real number $p$, and integers $n$ and $L \ge
1$. Set the rate
\[
r \;=\; 1 - H_q(p) - \frac{1}{L},
\]
and define
\[
M \;=\; \bigl\lfloor q^{\,r n} \bigr\rfloor,
\qquad
V \;=\; \bigl\lfloor q^{\,H_q(p)\, n} \bigr\rfloor .
\]
Assume that $0 < M \le q^n$ and $L < M$. Then
\[
q^n \cdot \binom{V}{L+1} \cdot \binom{q^n - (L+1)}{\,M - (L+1)\,}
\;<\;
\binom{q^n}{M}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Counting inequality for list decoding**: for the given choice of rate `r` and ball-size bound `V`, the number of "bad" `M`-subsets exceeds the number of good ones only if `M` is small (i.e., rate > capacity). -/
lemma ErrorCorrectingCodes.Codeword.listDecoding_counting_ineq
  (q : ℕ) (p : ℝ) (n L : ℕ)
  (hq : 2 ≤ q)
  (hL : 1 ≤ L)
  (r : ℝ) (hr : r = 1 - (qaryEntropy q p) - 1 / (L : ℝ))
  (M : ℕ) (hM : M = Nat.floor ((q : ℝ) ^ (r * n)))
  (V : ℕ) (hV : V = Nat.floor (Real.rpow q ((qaryEntropy q p) * n)))
  (hM_pos : 0 < M)
  (hM_le : M ≤ q^n)
  (hL_lt_M : L < M) :
  (q : ℝ)^n * (Nat.choose V (L+1)) * (Nat.choose (q^n - (L+1)) (M - (L+1))) < Nat.choose (q^n) M := by
    have h_binom_ratio : (Nat.choose (q ^ n - (L + 1)) (M - (L + 1)) : ℝ) / (Nat.choose (q ^ n) M) ≤ ((M : ℝ) / (q ^ n)) ^ (L + 1) := by
      convert binom_ratio_bound ( q ^ n ) M ( L + 1 ) _ _ using 1;
      · norm_cast;
      · linarith;
      · linarith;
    have h_binom_bound : (Nat.choose V (L + 1) : ℝ) ≤ (V : ℝ) ^ (L + 1) / (Nat.factorial (L + 1)) := by
      exact Nat.choose_le_pow_div (L + 1) V;
    have h_combined : (q ^ n : ℝ) * ((V : ℝ) ^ (L + 1) / (Nat.factorial (L + 1))) * ((M : ℝ) / (q ^ n)) ^ (L + 1) < 1 := by
      have h_simplified : (q : ℝ) ^ (-n / (L : ℝ)) / (Nat.factorial (L + 1)) < 1 := by
        rw [ div_lt_iff₀ ] <;> norm_num [ Nat.factorial_pos ];
        exact lt_of_le_of_lt ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) <| div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ ) <| by norm_num; linarith [ show ( L + 1 : ℝ ) ≥ 2 by norm_cast; linarith, show ( Nat.factorial ( L + 1 ) : ℝ ) ≥ L + 1 by exact_mod_cast Nat.self_le_factorial _ ] ;
      have h_subst : (q : ℝ) ^ n * ((q : ℝ) ^ (qaryEntropy q p * n)) ^ (L + 1) * ((q : ℝ) ^ (r * n) / (q ^ n)) ^ (L + 1) / (Nat.factorial (L + 1)) < 1 := by
        convert h_simplified using 1 ; rw [ hr ] ; ring_nf ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg q ) ] ; ring_nf;
        norm_num [ Real.rpow_add ( by positivity : 0 < ( q : ℝ ) ), Real.rpow_sub ( by positivity : 0 < ( q : ℝ ) ), Real.rpow_neg ( by positivity : 0 ≤ ( q : ℝ ) ) ] ; ring_nf;
        field_simp
        ring_nf;
        norm_cast ; norm_num [ pow_mul', mul_assoc, ne_of_gt ( zero_lt_two.trans_le hq ) ];
        rw [ ← div_eq_mul_inv, div_eq_iff ( by positivity ) ] ; ring;
      refine' lt_of_le_of_lt _ h_subst;
      rw [ mul_div_right_comm ];
      rw [ mul_div_assoc ];
      gcongr;
      · exact_mod_cast hV.symm ▸ Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      · exact_mod_cast hM.symm ▸ Nat.floor_le ( by positivity );
    rw [ div_le_iff₀ ] at h_binom_ratio;
    · refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left h_binom_ratio <| by positivity ) _;
      refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_binom_bound <| by positivity ) <| by positivity ) _;
      convert mul_lt_mul_of_pos_right h_combined ( Nat.cast_pos.mpr <| Nat.choose_pos hM_le ) using 1 ; ring;
      ring;
    · exact Nat.cast_pos.mpr ( Nat.choose_pos hM_le )
