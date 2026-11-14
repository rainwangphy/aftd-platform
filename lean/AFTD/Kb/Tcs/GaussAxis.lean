import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis

/-!
# gaussAxis

Topic: quantum   Node: 530b38756a6a

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

The standard Bloch axis order X, Y, Z.
-/

/-- The Bloch axis order X, Y, Z as a map Fin 3 → PauliBasis. -/
noncomputable def gaussAxis : Fin 3 → PauliBasis := ![PauliBasis.X, PauliBasis.Y, PauliBasis.Z]
