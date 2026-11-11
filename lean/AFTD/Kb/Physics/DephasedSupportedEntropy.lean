import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel
import AFTD.Kb.Physics.DephasedSupportedProb

/-!
# dephased_supported_entropy

Topic: quantum_mechanics   Node: f1535bb2058f

Provenance: helper lemma. Supported-kernel form of the entropy in OP-827, numerically compared with the original in experiment 22398.

The subsystem entropy expression formed from only the supported cut kernel and its character distribution.
-/

noncomputable def dephased_supported_entropy {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V) : ℝ := open scoped Classical BigOperators in (S.card : ℝ) - (Module.finrank (ZMod 2) (dephased_supported_kernel G q S) : ℝ) - ∑ χ : AddChar (dephased_supported_kernel G q S) ℝ, let p := dephased_supported_prob G q S χ; if p = 0 then 0 else p * Real.logb 2 p
