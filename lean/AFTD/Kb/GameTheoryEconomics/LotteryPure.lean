import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Lottery.pure

Topic: general_equilibrium   Node: a0b53ee232a1

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure (degenerate) lottery: outcome `o₀` with probability 1. Alias of `stdSimplex.pure`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- A pure (degenerate) lottery: outcome `o₀` with probability 1. Alias of `stdSimplex.pure`. -/
abbrev Lottery.pure {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    Lottery 𝕜 O :=
  stdSimplex.pure o₀
