import AFTD.Prelude

/-!
# Halving.log_succ_le_log_of_double_le

Topic: learning   Node: 3cb59c53dfe2

Provenance: helper lemma. TCSlib, `Halving.log_succ_le_log_of_double_le`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Logarithm increment under doubling. For natural numbers $a$ and $b$ with $b > 0$ and $2b \le a$,
\[
  \lfloor \log_2 b \rfloor + 1 \;\le\; \lfloor \log_2 a \rfloor,
\]
where $\lfloor \log_2 \cdot \rfloor$ denotes the integer (floor) base-$2$ logarithm.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- If `b` is positive and `2 · b ≤ a`, then `⌊log₂ b⌋ + 1 ≤ ⌊log₂ a⌋` (floors of base-2 logarithms, as computed by `Nat.log`): doubling spends exactly one unit of logarithmic budget. Arithmetic glue for `mistakes_bound`, with no textbook counterpart. -/
lemma Halving.log_succ_le_log_of_double_le {a b : ℕ}
    (hb : 0 < b) (hhalve : 2 * b ≤ a) :
    Nat.log 2 b + 1 ≤ Nat.log 2 a := by
  have hbne : b ≠ 0 := by omega
  have hpowlog : 2 ^ Nat.log 2 b ≤ b :=
    Nat.pow_log_le_self 2 hbne
  have hpow : 2 ^ (Nat.log 2 b + 1) ≤ a := by
    calc
      2 ^ (Nat.log 2 b + 1)
          = 2 ^ Nat.log 2 b * 2 := by
              rw [pow_succ]
      _ ≤ b * 2 := Nat.mul_le_mul_right 2 hpowlog
      _ = 2 * b := by omega
      _ ≤ a := hhalve
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
