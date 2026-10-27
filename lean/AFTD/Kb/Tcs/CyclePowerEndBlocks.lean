import AFTD.Prelude

/-!
# cycle_power_end_blocks

Topic: combinatorics   Node: 033025709581

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

The union of the first and last a integer positions of a class with origin p and arc length D.
-/

open Finset

def cycle_power_end_blocks (D a p u : ℤ) : Prop := (p ≤ u ∧ u < p + a) ∨ (p + D - a ≤ u ∧ u < p + D)
