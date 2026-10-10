import AFTD.Prelude

/-!
# CondensedMatter.TightBindingChain

Topic: condensed_matter   Node: 4dba4251e1d3

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The physical parameters making up the tight binding chain.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The physical parameters making up the tight binding chain. -/
structure CondensedMatter.TightBindingChain where
  /-- The number of sites, or atoms, in the chain -/
  N : Nat
  [N_ne_zero : NeZero N]
  /-- The distance between the sites -/
  a : ℝ
  a_pos : 0 < a
  /-- The energy associate with a particle sitting at a fixed site. -/
  E0 : ℝ
  /-- The hopping parameter. -/
  t : ℝ
