import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.binom_ratio_bound

Topic: information   Node: 9c7cdcaeeb5d

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.binom_ratio_bound`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/ListDecoding.lean (Apache-2.0); 1 verbatim; compiled here.

Binomial ratio bound. Let $N$, $M$, and $k$ be natural numbers with $k \le M \le N$. Then the ratio of
binomial coefficients satisfies
\[
\frac{\binom{N-k}{M-k}}{\binom{N}{M}} \;\le\; \left(\frac{M}{N}\right)^{k},
\]
where the quantities are compared as real numbers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Binomial ratio bound**: `C(N−k, M−k) / C(N, M) ≤ (M/N)ᵏ`. -/
lemma ErrorCorrectingCodes.Codeword.binom_ratio_bound (N M k : ℕ) (hM : M ≤ N) (hk : k ≤ M) :
  (Nat.choose (N - k) (M - k) : ℝ) / (Nat.choose N M) ≤ ((M : ℝ) / N) ^ k := by
    have h_prod : ((Nat.choose (N - k) (M - k)) : ℝ) / (Nat.choose N M) = Finset.prod (Finset.range k) (fun i => ((M - i) : ℝ) / ((N - i) : ℝ)) := by
      rw [ div_eq_iff ];
      · have h_binom : (Nat.choose (N - k) (M - k) : ℝ) * (Nat.choose N k : ℝ) = (Nat.choose N M : ℝ) * (Nat.choose M k : ℝ) := by
          rw_mod_cast [ Nat.choose_mul ] <;> try omega;
          ring;
        have h_binom_fact : (Nat.choose M k : ℝ) = (∏ i ∈ Finset.range k, (M - i : ℝ)) / (Nat.factorial k) ∧ (Nat.choose N k : ℝ) = (∏ i ∈ Finset.range k, (N - i : ℝ)) / (Nat.factorial k) := by
          constructor <;> rw [ eq_div_iff ( by positivity ) ];
          · rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ];
            rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
          · rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ];
            rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
        by_cases h : ( ∏ i ∈ Finset.range k, ( N - i : ℝ ) ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_comm, Finset.prod_mul_distrib ];
        · exact absurd h_binom_fact.2 <| ne_of_gt <| Nat.choose_pos <| by linarith;
        · field_simp at *;
          convert h_binom using 1;
      · exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.choose_pos hM;
    have h_le : ∀ i ∈ Finset.range k, ((M - i) : ℝ) / ((N - i) : ℝ) ≤ (M : ℝ) / N := by
      intro i hi; rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( i : ℝ ) + 1 ≤ M by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( M : ℝ ) ≤ N by norm_cast ] ;
    simpa only [ h_prod, Finset.prod_const, Finset.card_range ] using Finset.prod_le_prod ( fun _ _ => div_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| by linarith [ Finset.mem_range.1 ‹_› ] ) ( sub_nonneg.2 <| Nat.cast_le.2 <| by linarith [ Finset.mem_range.1 ‹_› ] ) ) h_le
