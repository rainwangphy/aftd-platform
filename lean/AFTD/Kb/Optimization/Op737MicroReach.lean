import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachableMicro

/-!
# op737_micro_reach

Topic: submodular   Node: 37fbff7cc4fb

Provenance: helper lemma. step towards op_737_block_capacity_submodular_and_base_polytope

The set of microstates reachable from the initial state x by Gibbs-stochastic maps: z is in op737_micro_reach γ x iff there is a Gibbs-stochastic matrix T with z = T x.
-/

/-- The set of microstates reachable from x by Gibbs-stochastic maps. -/
noncomputable def op737_micro_reach {n : ℕ} (γ x : Fin n → ℝ) : Set (Fin n → ℝ) := {z | thermally_reachable_micro γ x z}
