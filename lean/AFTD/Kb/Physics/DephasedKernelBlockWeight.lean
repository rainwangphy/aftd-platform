import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel

/-!
# dephased_kernel_block_weight

Topic: quantum_mechanics   Node: 1c11911c97f9

Provenance: helper lemma. Equality-block polynomial for the supported-kernel reduction of OP-827, tested in experiments 22410 and 22412.

The sum of parameter products over nonzero supported cut-kernel vectors whose supports are inclusion-minimal.
-/

noncomputable def dephased_kernel_block_weight {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V) : ℝ := open scoped Classical BigOperators in ∑ x : dephased_supported_kernel G q S, if x ≠ 0 ∧ (∀ y : dephased_supported_kernel G q S, y ≠ 0 → (∀ i : ↥S, y.1 i = 1 → x.1 i = 1) → y = x) then (∏ i ∈ Finset.univ.filter (fun i : ↥S => x.1 i = 1), q i.1) else 0
