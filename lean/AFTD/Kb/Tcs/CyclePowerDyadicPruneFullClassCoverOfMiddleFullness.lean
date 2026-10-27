import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicHalfOwnerFullPruneOfMiddle
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_full_class_cover_of_middle_fullness

Topic: combinatorics   Node: 44694dbb44cb

Provenance: helper lemma. Routine bridge for OP-205 / RT-1 fullness induction. The stronger idea that full classes at every vertex force general shape remains conjectural; reduced-neighbour shortcuts have guarded countermodels in experiment6657.

Current-scale middle-bit fullness ensures that every vertex of the pruned model lies in a full pruned class. Fullness and half-distance coverage remain explicit; no count preservation is asserted.
-/

open Finset

theorem cycle_power_dyadic_prune_full_class_cover_of_middle_fullness
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hcover : ∀ v : ℤ, ∃ a : ℕ, a < 2^(k+1) ∧
      x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+2^(k+1)) = true) :
    ∀ v : ℤ, ∃ a : ℕ, a < 2^(k+1) ∧
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x (v-(a : ℤ))) i = true := by
  intro v
  rcases hcover v with ⟨a, ha, h0, h1⟩
  exact ⟨a, ha, cycle_power_dyadic_half_owner_full_prune_of_middle k x hmid (v - (a : ℤ)) a ha h0 h1⟩
