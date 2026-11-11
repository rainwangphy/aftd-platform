import AFTD.Prelude
import AFTD.Kb.Physics.DephasedBinaryKernelNullity

/-!
# dephased_binary_kernel_gap

Topic: quantum_mechanics   Node: 516eda793413

Provenance: helper lemma. Binary-support rank formulation for OP-827.

Tripartite alternating sum of binary-supported cut-kernel dimensions.
-/

noncomputable def dephased_binary_kernel_gap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (P A B C : Finset V) : ℤ := (dephased_binary_kernel_nullity G P A : ℤ) + dephased_binary_kernel_nullity G P B + dephased_binary_kernel_nullity G P C - dephased_binary_kernel_nullity G P (A ∪ B) - dephased_binary_kernel_nullity G P (A ∪ C) - dephased_binary_kernel_nullity G P (B ∪ C) + dephased_binary_kernel_nullity G P (A ∪ B ∪ C)
