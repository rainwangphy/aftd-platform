import AFTD.Prelude

/-!
# stdSimplex.upidx

Topic: general_equilibrium   Node: c0b05a1a53bc

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.upidx`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

stdSimplex.upidx
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) in
variable {n l} in
noncomputable instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
  by_contra h
  push Not at h
  have sum_x_eq_1 := x.2.2
  have sum_y_eq_1 := y.2.2
  have sum_lt : Finset.sum Finset.univ y.1 < Finset.sum Finset.univ x.1 := by
    apply Finset.sum_lt_sum_of_nonempty
    . exact Finset.univ_nonempty
    . intro i _
      have : ¬ (x.1 i ≤ y.1 i) := by
        intro hle
        exact @IsEmpty.false _ h ⟨i, hle⟩
      exact lt_of_not_ge this
  rw [sum_y_eq_1, sum_x_eq_1] at sum_lt
  exact (lt_irrefl 1 sum_lt).elim
