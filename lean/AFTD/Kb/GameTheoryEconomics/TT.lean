import AFTD.Prelude

/-!
# TT

Topic: general_equilibrium   Node: bbc0ba9b8a2b

Provenance: formalization of a published result. Source: EconCSLib, `TT`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TT
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
noncomputable abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}
