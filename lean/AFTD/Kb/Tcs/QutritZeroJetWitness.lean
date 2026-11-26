import AFTD.Prelude
import AFTD.Kb.Tcs.QutritZeroJetFlatWitness

/-!
# qutrit_zero_jet_witness

Topic: quantum   Node: 4783a1b36fc8

Provenance: helper lemma. OP-2299; coordinate-zero local jet, experiments 40338, 40339, and 40344.

The same zero-coordinate witness in bipartite indices.
-/

noncomputable def qutrit_zero_jet_witness (b c : ℝ) (u v q : ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun p r => qutrit_zero_jet_flat_witness b c u v q ⟨3 * p.1.val + p.2.val, by omega⟩ ⟨3 * r.1.val + r.2.val, by omega⟩
