import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenState

/-!
# bit_persuasion_even_prior

Topic: mechanism_design   Node: b926502e699e

Provenance: formalization of a published result. Source: arXiv:2606.22226

The function bit_persuasion_even_prior m of type (bit_persuasion_even_coord m → Bool) → ℝ mapping each configuration x to the sum over all s : Fin (2 * m) of 1 / (2 * m : ℝ) if bit_persuasion_even_state m s = x and 0 otherwise.
-/

open Finset in
/-- The two-layer prior on 2m states: uniform distribution over the 2m states bit_persuasion_even_state m s. -/
noncomputable def bit_persuasion_even_prior (m : ℕ) : (bit_persuasion_even_coord m → Bool) → ℝ :=
  fun x => ∑ s, if bit_persuasion_even_state m s = x then 1 / (2 * m : ℝ) else 0
