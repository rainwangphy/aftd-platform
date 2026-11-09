import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreVarSize

/-!
# hard_core_weighted_var_ones

Topic: statistical_mechanics   Node: 3add33069245

Provenance: helper lemma. folklore

When the observable weights a are identically 1, the weighted hard-core variance hardCoreWeightedVar G lam (fun _ => 1) is equal to the unweighted independent set size variance hardCoreVarSize G lam.
-/

/-- Specializing weighted hard-core variance to constant observable weight 1 recovers the independent set size variance. -/
theorem hard_core_weighted_var_ones {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) :
    hardCoreWeightedVar G lam (fun _ => 1) = hardCoreVarSize G lam := by
  unfold hardCoreWeightedVar hardCoreVarSize
  simp
