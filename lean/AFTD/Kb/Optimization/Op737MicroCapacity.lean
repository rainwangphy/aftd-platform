import AFTD.Prelude
import AFTD.Kb.Optimization.Op737MicroReach

/-!
# op737_micro_capacity

Topic: submodular   Node: 62c173e0bd81

Provenance: helper lemma. step towards op_737_block_capacity_submodular_and_base_polytope

The micro-capacity of a set A of microstates: the supremum, over all microstates z reachable from x, of the total population of A in z.
-/

/-- The micro-capacity: supremum of the population of A over reachable microstates. -/
noncomputable def op737_micro_capacity {n : ℕ} (γ x : Fin n → ℝ) (A : Finset (Fin n)) : ℝ := sSup ((fun z : Fin n → ℝ => ∑ i ∈ A, z i) '' op737_micro_reach γ x)
