import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMClog2FloorHalfLe
import AFTD.Kb.Tcs.CslibAlgorithmsLeanTimeMClog2HalfLe

/-!
# Cslib.Algorithms.Lean.TimeM.some_algebra

Topic: algorithms   Node: 4324a82da7b5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM.some_algebra`. Lean proof by Sorrachai Yingchareonthawornhcai, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Algorithms.Lean.TimeM.some_algebra
-/

set_option relaxedAutoImplicit true in
set_option autoImplicit false in
variable {α : Type} [LinearOrder α] in
open Nat (clog) in
lemma Cslib.Algorithms.Lean.TimeM.some_algebra (n : ℕ) :
    (n / 2 + 1) * clog 2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog 2 ((n + 1) / 2 + 1) + (n + 2) ≤
    (n + 2) * clog 2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : N ≥ 2 := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  let k := clog 2 N
  have h_bound_l : clog 2 (N / 2) ≤ k - 1 := clog2_floor_half_le N hN
  have h_bound_r : clog 2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N hN
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  grw [t1, t2, t3, h_bound_l, h_bound_r, ←Nat.add_mul, h_split]
  exact Nat.le_refl (N * (k - 1) + N)
