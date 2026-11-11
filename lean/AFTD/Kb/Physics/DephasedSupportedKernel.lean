import AFTD.Prelude
import AFTD.Kb.Physics.TreeSubmatrixKer

/-!
# dephased_supported_kernel

Topic: quantum_mechanics   Node: 48c8b30f10ae

Provenance: helper lemma. Supported-kernel reduction of the dephased entropy in OP-827; tested in experiment 22398.

The part of the cut kernel whose vectors vanish at every zero-parameter vertex of the subsystem.
-/

noncomputable def dephased_supported_kernel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V) : Submodule (ZMod 2) (↥S → ZMod 2) := tree_submatrix_ker G S ⊓ { carrier := {x | ∀ i : ↥S, q i.1 = 0 → x i = 0}, zero_mem' := by simp, add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi], smul_mem' := by intro a x hx i hi; simp [hx i hi] }
