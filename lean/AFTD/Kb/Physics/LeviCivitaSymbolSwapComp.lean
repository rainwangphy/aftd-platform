import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.LeviCivitaSymbolEqDet
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.Physics.LeviCivitaSymbolPerm

/-!
# leviCivitaSymbol_swap_comp

Topic: classical_mechanics   Node: 1eb75a361867

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_swap_comp`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol is antisymmetric under transposition of two index values: postcomposing with the swap of two distinct values exchanges those two values wherever they occur and negates it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
set_option backward.isDefEq.respectTransparency false in
/-- The Levi-Civita symbol is antisymmetric under transposition of two index values: postcomposing with the swap of two distinct values exchanges those two values wherever they occur and negates it. -/
lemma leviCivitaSymbol_swap_comp (g : ι → ι) {i j : ι} (hij : i ≠ j) :
    leviCivitaSymbol (Equiv.swap i j ∘ g) = - leviCivitaSymbol g := by
  have h : (fun a b => ((kroneckerDelta ((Equiv.swap i j ∘ g) a) b : ℕ) : ℤ))
      = Matrix.submatrix (fun a b => ((kroneckerDelta (g a) b : ℕ) : ℤ)) id (Equiv.swap i j) :=
    funext fun a => funext fun b => by simp [kroneckerDelta, Equiv.swap_apply_eq_iff]
  rw [leviCivitaSymbol_eq_det, h, Matrix.det_permute', Equiv.Perm.sign_swap hij,
    ← leviCivitaSymbol_eq_det]
  simp
