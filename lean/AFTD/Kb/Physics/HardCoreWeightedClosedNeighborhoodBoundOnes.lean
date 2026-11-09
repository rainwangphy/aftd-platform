import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound
import AFTD.Kb.Physics.HardCoreClosedNeighborhoodBound
import AFTD.Kb.Physics.HardCoreWeightedVarOnes

/-!
# hard_core_weighted_closed_neighborhood_bound_ones

Topic: statistical_mechanics   Node: a1bf5147e49e

Provenance: helper lemma. folklore

When the observable weights a are identically 1, the weighted closed-neighborhood bound hardCoreWeightedClosedNeighborhoodBound G lam (fun _ => 1) is equal to the unweighted closed-neighborhood bound hardCoreClosedNeighborhoodBound G lam.
-/

/-- Specializing the weighted closed-neighborhood bound to constant observable weight 1 recovers the unweighted bound. -/
theorem hard_core_weighted_closed_neighborhood_bound_ones {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) :
    hardCoreWeightedClosedNeighborhoodBound G lam (fun _ => 1) = hardCoreClosedNeighborhoodBound G lam := by first | exact hard_core_weighted_var_ones | (apply hard_core_weighted_var_ones <;> assumption) | (apply hard_core_weighted_var_ones <;> simp_all) | simpa using hard_core_weighted_var_ones | (simp only [hardCoreClosedNeighborhoodBound, hardCoreWeightedClosedNeighborhoodBound] at *; first | exact hard_core_weighted_var_ones | (apply hard_core_weighted_var_ones <;> assumption) | (apply hard_core_weighted_var_ones <;> simp_all) | simpa using hard_core_weighted_var_ones)
