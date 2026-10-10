import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.LeviCivitaSymbolEqDet
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm

/-!
# leviCivitaSymbol_id

Topic: classical_mechanics   Node: 228eff268fc5

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_id`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol of the identity, i.e. `ε_{0 1 ⋯ (d-1)}`, is `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol of the identity, i.e. `ε_{0 1 ⋯ (d-1)}`, is `1`. -/
@[simp]
lemma leviCivitaSymbol_id : leviCivitaSymbol (id : ι → ι) = 1 := by
  rw [leviCivitaSymbol_eq_det, show (fun i j => ((kroneckerDelta (id i : ι) j : ℕ) : ℤ))
    = (1 : Matrix ι ι ℤ) from funext fun i => funext fun j => by
      simp [kroneckerDelta, Matrix.one_apply]]
  exact Matrix.det_one
