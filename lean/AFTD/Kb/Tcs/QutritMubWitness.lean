import AFTD.Prelude
import AFTD.Kb.Tcs.QutritMubWitnessFlat

/-!
# qutrit_mub_witness

Topic: quantum   Node: 18d907d1ab6e

Provenance: helper lemma. OP-2299; partial transpose of the explicit optimal witness from https://arxiv.org/abs/2503.04158, Eq. 14; exact SOS experiments 40358 and 40360.

The same invariant witness in bipartite matrix indices.
-/

noncomputable def qutrit_mub_witness : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun p r => qutrit_mub_witness_flat ⟨3 * p.1.val + p.2.val, by omega⟩ ⟨3 * r.1.val + r.2.val, by omega⟩
