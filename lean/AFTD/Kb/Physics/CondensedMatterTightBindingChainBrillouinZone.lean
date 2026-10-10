import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain

/-!
# CondensedMatter.TightBindingChain.BrillouinZone

Topic: condensed_matter   Node: 963bc5d37a65

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.BrillouinZone`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Brillouin zone of the tight binding model is `[-π/a, π/a)`. This is the set in which wave functions are uniquely defined.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter in
open InnerProductSpace in
variable (T : TightBindingChain) in
/-- The Brillouin zone of the tight binding model is `[-π/a, π/a)`. This is the set in which wave functions are uniquely defined. -/
def CondensedMatter.TightBindingChain.BrillouinZone : Set ℝ := Set.Ico (- Real.pi / T.a) (Real.pi / T.a)
