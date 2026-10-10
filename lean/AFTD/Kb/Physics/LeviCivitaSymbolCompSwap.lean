import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaSwap
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.Physics.LeviCivitaSymbolPerm

/-!
# leviCivitaSymbol_comp_swap

Topic: classical_mechanics   Node: 8968109ac95d

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_comp_swap`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol is antisymmetric under transposition of two of its indices: precomposing with the swap of two distinct index positions negates it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol is antisymmetric under transposition of two of its indices: precomposing with the swap of two distinct index positions negates it. -/
lemma leviCivitaSymbol_comp_swap (g : ι → ι) {i j : ι} (hij : i ≠ j) :
    leviCivitaSymbol (g ∘ Equiv.swap i j) = - leviCivitaSymbol g :=
  generalizedKroneckerDelta_swap g id hij
