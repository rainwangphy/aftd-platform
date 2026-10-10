import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm

/-!
# leviCivitaSymbol_eq_det

Topic: classical_mechanics   Node: d2780d760aac

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_eq_det`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol as the determinant of the matrix of Kronecker deltas `δ[g i, j]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol as the determinant of the matrix of Kronecker deltas `δ[g i, j]`. -/
lemma leviCivitaSymbol_eq_det (g : ι → ι) :
    leviCivitaSymbol g = Matrix.det (fun i j => ((kroneckerDelta (g i) j : ℕ) : ℤ)) :=
  rfl
