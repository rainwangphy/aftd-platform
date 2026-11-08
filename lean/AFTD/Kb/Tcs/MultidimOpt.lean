import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule

/-!
# multidim_opt

Topic: online_algorithms   Node: 5fe58a66a649

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.1

The offline optimal total completion time multidim_opt I of a multidimensional scheduling instance I with D resources is defined as the real infimum sInf of the set of all s such that there exist a rate allocation x and completion times C satisfying multidim_is_feasible_schedule I x C with s = ∑ j, C j.
-/

/-- Offline optimal total completion time for a multidimensional scheduling instance. -/
noncomputable def multidim_opt {D : ℕ} (I : MultidimInstance D) : ℝ :=
  sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule I x C ∧ s = ∑ j, C j }
