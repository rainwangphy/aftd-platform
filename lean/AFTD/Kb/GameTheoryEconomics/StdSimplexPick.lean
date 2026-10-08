import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StdSimplexUpidx

/-!
# stdSimplex.pick

Topic: general_equilibrium   Node: df8fab3dcdfb

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.pick`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

stdSimplex.pick
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) in
variable {n l} in
noncomputable def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y
