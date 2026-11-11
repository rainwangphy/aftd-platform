import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel

/-!
# dephased_supported_prob

Topic: quantum_mechanics   Node: fcdb5dd23995

Provenance: helper lemma. Supported-kernel character distribution for the entropy reduction in OP-827.

The normalized character transform on the part of the cut kernel supported at nonzero parameters.
-/

noncomputable def dephased_supported_prob {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V) (χ : AddChar (dephased_supported_kernel G q S) ℝ) : ℝ := open scoped Classical BigOperators in (1 / 2 : ℝ) ^ (Module.finrank (ZMod 2) (dephased_supported_kernel G q S)) * ∑ x : dephased_supported_kernel G q S, χ x * ∏ i ∈ Finset.univ.filter (fun i : ↥S => x.1 i = 1), q i.1
