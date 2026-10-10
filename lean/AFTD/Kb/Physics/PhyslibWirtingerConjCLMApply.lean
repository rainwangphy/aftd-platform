import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerConjCLM

/-!
# Physlib.Wirtinger.conjCLM_apply

Topic: classical_mechanics   Node: b4ba4969bd26

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.conjCLM_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Wirtinger.conjCLM_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma Physlib.Wirtinger.conjCLM_apply (u : ι → ℂ) : conjCLM u = star u := rfl
