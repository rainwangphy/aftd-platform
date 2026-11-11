import AFTD.Prelude
import AFTD.Kb.Physics.TreeSubmatrixKer
import AFTD.Kb.Physics.DephasedSupportedKernel

/-!
# dephased_supported_character_restrict

Topic: quantum_mechanics   Node: f3504e751270

Provenance: helper lemma. Character restriction in the supported-entropy reduction for OP-827.

Restrict a character of the cut kernel to its supported subspace.
-/

noncomputable def dephased_supported_character_restrict {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V) (χ : AddChar (tree_submatrix_ker G S) ℝ) : AddChar (dephased_supported_kernel G q S) ℝ := χ.compAddMonoidHom ((Submodule.inclusion (show dephased_supported_kernel G q S ≤ tree_submatrix_ker G S from inf_le_left)).toAddMonoidHom)
