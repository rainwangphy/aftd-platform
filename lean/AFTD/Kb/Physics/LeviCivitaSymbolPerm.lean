import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.LeviCivitaSymbolEqDet
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.GameTheoryEconomics.GameTreeMemValueListIff

/-!
# leviCivitaSymbol_perm

Topic: classical_mechanics   Node: fa228ef2365e

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_perm`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol of a permutation `σ` is the sign of `σ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol of a permutation `σ` is the sign of `σ`. -/
@[simp]
lemma leviCivitaSymbol_perm (σ : Equiv.Perm ι) :
    leviCivitaSymbol ⇑σ = (Equiv.Perm.sign σ : ℤ) := by
  rw [leviCivitaSymbol_eq_det, show (fun i j => ((kroneckerDelta (σ i) j : ℕ) : ℤ))
    = σ.permMatrix ℤ from funext fun i => funext fun j => by
      simp [kroneckerDelta, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]]
  exact Matrix.det_permutation σ
