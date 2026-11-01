import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues

/-!
# efx_no_self_three_split_value

Topic: fair_division   Node: 44532d32bac5

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

The natural additive value to i of the goods in S.
-/

def efx_no_self_three_split_value (i : Fin 4) (S : Finset (Fin 13)) : ℕ := ∑ g ∈ S, efx_no_self_three_split_values i g
