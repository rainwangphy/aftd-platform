import AFTD.Prelude

/-!
# Nat.nth_succ_gap

Topic: algorithms   Node: 2dbaea515193

Provenance: formalization of a published result. Source: CSLib, `Nat.nth_succ_gap`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Nat/Segment.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There is a gap between two successive occurrences of a predicate `p : ℕ → Prop`, assuming `p` (as a set) is infinite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {f : ℕ → ℕ} in
/-- There is a gap between two successive occurrences of a predicate `p : ℕ → Prop`, assuming `p` (as a set) is infinite. -/
theorem Nat.nth_succ_gap {p : ℕ → Prop} (hf : (ofPred p).Infinite) (n : ℕ) :
    ∀ k < nth p (n + 1) - nth p n, k > 0 → ¬ p (k + nth p n) := by
  classical
  intro k h_k1 h_k0 h_p_k
  let m := count p (k + nth p n)
  have h_k_ex : nth p m = k + nth p n := by simp [m, nth_count h_p_k]
  have h_n_m : n < m := by apply (nth_lt_nth hf).mp; omega
  have h_m_n : m < n + 1 := by apply (nth_lt_nth hf).mp; omega
  omega
