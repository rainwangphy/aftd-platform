import AFTD.Prelude
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_generating_function

Topic: information   Node: c6646153db27

Provenance: helper lemma. TCSlib, `krawtchouk_generating_function`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 adapted; compiled here.

Generating function of the Krawtchouk polynomials. Let $n$ and $x$ be natural numbers with $x \le n$, and let $K_j^{(n)}(x)$ denote the
binary Krawtchouk polynomial. Then for every real $z$,
\[
  \sum_{j=0}^{n} K_j^{(n)}(x)\, z^{j} \;=\; (1-z)^{x}\,(1+z)^{\,n-x}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
theorem krawtchouk_generating_function (n x : ℕ) (hx : x ≤ n) (z : ℝ) :
    ∑ j ∈ Finset.range (n + 1), krawtchouk n j x * z ^ j =
      (1 - z) ^ x * (1 + z) ^ (n - x) := by
  -- The key identity is: ∑_{j=0}^{n} (∑_{i=0}^{j} (-1)^i C(x,i) C(n-x, j-i)) z^j = (1-z)^x (1+z)^{n-x}.
  have hKey : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j = (1 - z) ^ x * (1 + z) ^ (n - x) := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have hFubini : ∑ j ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j) = ∑ i ∈ Finset.range (x + 1), (-1 : ℝ) ^ i * Nat.choose x i * (∑ j ∈ Finset.Ico i (n + 1), Nat.choose (n - x) (j - i) * z ^ j) := by
      have hFubini : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico i (n + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j := by
        simp only [Finset.range_eq_Ico]; rw [ Finset.sum_Ico_Ico_comm ];
      rw [ hFubini, ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ hx ) ) ];
      · simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
      · intro k hk hxk
        have hzero : x.choose k = 0 :=
          Nat.choose_eq_zero_of_lt
            (Nat.not_le.mp (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hxk))
        simp [hzero];
    -- Let's simplify the inner sum $\sum_{j=i}^{n} \binom{n-x}{j-i} z^j$.
    have hInner : ∀ i ∈ Finset.range (x + 1), ∑ j ∈ Finset.Ico i (n + 1), Nat.choose (n - x) (j - i) * z ^ j = z ^ i * (1 + z) ^ (n - x) := by
      intro i hi; rw [ add_comm 1 z, add_pow ] ; simp +decide [ mul_comm, Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ] ;
      rw [ ← Finset.sum_subset ( Finset.range_mono ( show n - x + 1 ≤ n + 1 - i from by rw [ Nat.le_sub_iff_add_le ] <;> linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hx ] ) ) ] <;> simp +decide [ pow_add, mul_assoc ];
      exact fun j hj₁ hj₂ => Or.inr <| Or.inr <| Nat.choose_eq_zero_of_lt hj₂;
    rw [ hFubini, Finset.sum_congr rfl fun i hi => by rw [ hInner i hi ] ];
    rw [ show ( 1 - z ) ^ x = ∑ i ∈ Finset.range ( x + 1 ), ( -1 : ℝ ) ^ i * Nat.choose x i * z ^ i by rw [ sub_eq_neg_add, add_pow ] ; congr ; ext ; ring ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  simp_all +decide [ ← Finset.sum_mul, krawtchouk ]

/-
**Lemma 3 (orthogonality)** from the source file.
For `0 ≤ r, s ≤ n`,
  `∑_{x=0}^{n} C(n,x) · K_r(x) · K_s(x) = 2^n · C(n,r) · δ_{r,s}`.
-/
