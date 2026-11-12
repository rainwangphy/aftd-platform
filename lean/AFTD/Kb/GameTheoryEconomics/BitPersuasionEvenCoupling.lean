import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenState

/-!
# bit_persuasion_even_coupling

Topic: mechanism_design   Node: ebd87ab1b59e

Provenance: formalization of a published result. Source: arXiv:2606.22226

The function bit_persuasion_even_coupling m of type (bit_persuasion_even_coord m → Bool) → (bit_persuasion_even_coord m → Bool) → ℝ mapping each pair of configurations (x, y) to the sum over all s, t : Fin (2 * m) of 1 / ((2 * m : ℝ) * (2 * m - 1)) if s ≠ t and bit_persuasion_even_state m s = x and bit_persuasion_even_state m t = y, and 0 otherwise.
-/

open Finset in
/-- The coupling that pairs each realized state with a uniformly random different state among the 2m states. -/
noncomputable def bit_persuasion_even_coupling (m : ℕ) :
    (bit_persuasion_even_coord m → Bool) → (bit_persuasion_even_coord m → Bool) → ℝ :=
  fun x y => ∑ s, ∑ t, if s ≠ t ∧ bit_persuasion_even_state m s = x ∧ bit_persuasion_even_state m t = y
    then 1 / ((2 * m : ℝ) * (2 * m - 1)) else 0
