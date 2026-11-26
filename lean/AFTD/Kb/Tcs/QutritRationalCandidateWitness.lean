import AFTD.Prelude
import AFTD.Kb.Tcs.QutritRationalCandidateWitnessFlat

/-!
# qutrit_rational_candidate_witness

Topic: quantum   Node: 6f60209355b4

Provenance: helper lemma. OP-2299; candidate witness from computations 39270, 40213 and 40215.

The same candidate witness with tensor-product indices.
-/

noncomputable def qutrit_rational_candidate_witness : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun p q => qutrit_rational_candidate_witness_flat ⟨3 * p.1.val + p.2.val, by omega⟩ ⟨3 * q.1.val + q.2.val, by omega⟩
