import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain

/-!
# CondensedMatter.TightBindingChain.instNeZeroNatN

Topic: condensed_matter   Node: 480ae21bcdad

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.instNeZeroNatN`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CondensedMatter.TightBindingChain.instNeZeroNatN
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter in
open InnerProductSpace in
variable (T : TightBindingChain) in
instance CondensedMatter.TightBindingChain.instNeZeroNatN : NeZero T.N := T.N_ne_zero
