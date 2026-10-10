import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm

/-!
# leviCivitaSymbol

Topic: classical_mechanics   Node: 6e90fdae8c7f

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol on a finite index type `ι`: `leviCivitaSymbol g` is the sign of `g` when `g : ι → ι` is a permutation, and `0` otherwise. It is the generalized Kronecker delta of `g` against the identity, i.e. the determinant of the matrix of Kronecker deltas `δ[g i, j]`. For `ι = Fin d` this is the Levi-Civita symbol `ε_{i₁ ⋯ i_d}` in dimension `d`, normalized by `ε_{0 1 ⋯ (d-1)} = 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol on a finite index type `ι`: `leviCivitaSymbol g` is the sign of `g` when `g : ι → ι` is a permutation, and `0` otherwise. It is the generalized Kronecker delta of `g` against the identity, i.e. the determinant of the matrix of Kronecker deltas `δ[g i, j]`. For `ι = Fin d` this is the Levi-Civita symbol `ε_{i₁ ⋯ i_d}` in dimension `d`, normalized by `ε_{0 1 ⋯ (d-1)} = 1`. -/
def leviCivitaSymbol (g : ι → ι) : ℤ :=
  generalizedKroneckerDelta g (id : ι → ι)
