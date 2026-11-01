import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# additive_valuation_erase_of_mem

Topic: fair_division   Node: c4891c3d9781

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

Removing a good belonging to a finite bundle subtracts exactly its item value from the additive value of that bundle.
-/

open Function Finset

theorem additive_valuation_erase_of_mem {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (g : Fin m) (hg : g ∈ S) :
    additive_valuation u (S.erase g) = additive_valuation u S - u g := by
  exact eq_sub_iff_add_eq.mpr (Finset.sum_erase_add S u hg)
