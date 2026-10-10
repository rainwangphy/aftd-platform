import AFTD.Prelude

/-!
# SpaceTimeAlgebra

Topic: special_relativity   Node: d23b4ee09e10

Provenance: formalization of a published result. Source: Physlib, `SpaceTimeAlgebra`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/SpaceTime/SpaceTimeAlgebra/Basic.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Formal power series in the four spacetime directions, with complex coefficients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Formal power series in the four spacetime directions, with complex coefficients. -/
abbrev SpaceTimeAlgebra : Type := MvPowerSeries (Fin 1 ⊕ Fin 3) ℂ
