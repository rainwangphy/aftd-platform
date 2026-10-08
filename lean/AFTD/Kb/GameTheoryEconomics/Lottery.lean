import AFTD.Prelude

/-!
# Lottery

Topic: general_equilibrium   Node: 0fa626897b18

Provenance: formalization of a published result. Source: EconCSLib, `Lottery`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A lottery over outcomes `O`: a probability distribution. Just `stdSimplex 𝕜 O` with a game-theoretic name.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- A lottery over outcomes `O`: a probability distribution. Just `stdSimplex 𝕜 O` with a game-theoretic name. -/
abbrev Lottery (𝕜 : Type*) (O : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype O] :=
  stdSimplex 𝕜 O
