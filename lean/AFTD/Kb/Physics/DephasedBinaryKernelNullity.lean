import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel

/-!
# dephased_binary_kernel_nullity

Topic: quantum_mechanics   Node: d545ccd0e703

Provenance: helper lemma. Binary-support rank formulation for the OP-827 block-polynomial reduction.

The dimension of the cut kernel restricted to vectors supported on P.
-/

noncomputable def dephased_binary_kernel_nullity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (P S : Finset V) : ℕ := open scoped Classical in Module.finrank (ZMod 2) (dephased_supported_kernel G (fun v => if v ∈ P then 1 else 0) S)
