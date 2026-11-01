import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitExponents

/-!
# efx_no_self_three_split_perturbed_values

Topic: fair_division   Node: 5a7aae2699b4

Provenance: helper lemma. Nondegenerate strengthening of the OP-7 no-self three-split obstruction, experiments 11492–11494; related perturbation argument arXiv:2002.05119 Lemma 1.

The nondegenerate perturbation of the thirteen-good no-self three-split matrix.
-/

def efx_no_self_three_split_perturbed_values : Fin 4 → Fin 13 → ℕ := fun i g => 16384 * efx_no_self_three_split_values i g + 2 ^ efx_no_self_three_split_exponents i g
