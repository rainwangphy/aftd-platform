import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoord
import AFTD.Kb.GameTheoryEconomics.BitPersuasionEvenCoupling
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme

/-!
# bit_persuasion_even_scheme

Topic: mechanism_design   Node: 836590325189

Provenance: formalization of a published result. Source: arXiv:2606.22226

The direct signaling scheme bit_persuasion_even_scheme m of type (bit_persuasion_even_coord m → Bool) → (bit_persuasion_even_coord m → Bool) → ℝ defined as persuasion_pair_or_scheme applied to bit_persuasion_even_coupling m.
-/

open Finset in
/-- The pair-OR signaling scheme for the two-layer construction: draw a pair of distinct states containing the realized state and recommend their coordinatewise OR. -/
noncomputable def bit_persuasion_even_scheme (m : ℕ) :
    (bit_persuasion_even_coord m → Bool) → (bit_persuasion_even_coord m → Bool) → ℝ :=
  persuasion_pair_or_scheme (bit_persuasion_even_coupling m)
