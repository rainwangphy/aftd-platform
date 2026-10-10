import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.LeviCivitaSymbolPerm
import AFTD.Kb.Physics.LeviCivitaSymbolEqZeroOfNotInjective
import AFTD.Kb.Physics.KroneckerDeltaSymm
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapNeLossIff
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# leviCivitaSymbol_eq_prod_prod_Ioi

Topic: classical_mechanics   Node: a7df48c42b71

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_eq_prod_prod_Ioi`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On `Fin n` the Levi-Civita symbol is the product over pairs `i < j` of the sign of `g j - g i`. Unlike the determinant defining `leviCivitaSymbol`, this product is cheap to evaluate, e.g. by `decide`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- On `Fin n` the Levi-Civita symbol is the product over pairs `i < j` of the sign of `g j - g i`. Unlike the determinant defining `leviCivitaSymbol`, this product is cheap to evaluate, e.g. by `decide`. -/
lemma leviCivitaSymbol_eq_prod_prod_Ioi {n : ℕ} (g : Fin n → Fin n) :
    leviCivitaSymbol g =
      ∏ i, ∏ j ∈ Finset.Ioi i, (if g i < g j then 1 else if g i = g j then 0 else -1) := by
  by_cases hg : Function.Injective g
  · obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin n), ⇑σ = g :=
      ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), rfl⟩
    rw [leviCivitaSymbol_perm, Equiv.Perm.sign_eq_prod_prod_Ioi]
    simp only [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : σ i ≠ σ j := σ.injective.ne (Finset.mem_Ioi.mp hj).ne
    split_ifs <;> simp
  · rw [leviCivitaSymbol_eq_zero_of_not_injective hg]
    simp only [Function.Injective, not_forall] at hg
    obtain ⟨i, j, hgij, hij⟩ := hg
    symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact Finset.prod_eq_zero (Finset.mem_univ i)
        (Finset.prod_eq_zero (Finset.mem_Ioi.mpr h) (by simp [hgij]))
    · exact Finset.prod_eq_zero (Finset.mem_univ j)
        (Finset.prod_eq_zero (Finset.mem_Ioi.mpr h) (by simp [hgij]))
