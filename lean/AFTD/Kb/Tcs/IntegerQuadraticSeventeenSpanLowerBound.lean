import AFTD.Prelude

/-!
# integer_quadratic_seventeen_span_lower_bound

Topic: combinatorics   Node: b34f66884800

Provenance: helper lemma. Endpoint calculation for the integer quadratic route to OP-1482.

If all first 17 values of an integer quadratic with nonnegative leading coefficient q lie between L and U, then U−L is at least 64q.
-/

theorem integer_quadratic_seventeen_span_lower_bound (q a b L U : ℤ) (hq : 0 ≤ q) (h : ∀ k : Fin 17, L ≤ q * (k.val : ℤ)^2 + a * k.val + b ∧ q * (k.val : ℤ)^2 + a * k.val + b ≤ U) : 64 * q ≤ U - L := by
  have h0 := h ⟨0, by decide⟩
  have h8 := h ⟨8, by decide⟩
  have h16 := h ⟨16, by decide⟩
  norm_num at h0 h8 h16
  omega
