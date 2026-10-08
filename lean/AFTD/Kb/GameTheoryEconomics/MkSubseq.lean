import AFTD.Prelude

/-!
# mk_subseq

Topic: general_equilibrium   Node: 505072e60850

Provenance: formalization of a published result. Source: EconCSLib, `mk_subseq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

mk_subseq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) in
variable {n l} in
noncomputable def mk_subseq (f : ℕ → ℕ) (h : ∀ n, n < f n) : ℕ → ℕ
  | 0 => f 0
  | n+1 => f (mk_subseq f h n)
