import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.ext

Topic: classical_mechanics   Node: c45e5200e666

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.ext`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib in
open scoped BigOperators in
variable {d : ℕ} in
@[ext]
lemma Physlib.MultiIndex.ext {I J : MultiIndex d} (h : ∀ i, I i = J i) : I = J := by
  cases I
  cases J
  simp only at h
  congr
  funext i
  exact h i
