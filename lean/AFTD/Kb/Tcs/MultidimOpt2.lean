import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2
import AFTD.Kb.Tcs.MultidimIsFeasibleSchedule2

/-!
# multidim_opt2

Topic: online_algorithms   Node: cae6b241cfab

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.1

The offline optimal total completion time multidim_opt2 I of a two-resource multidimensional scheduling instance I is defined as sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule2 I x C ∧ s = ∑ j, C j }.
-/

/-- Offline optimal total completion time for a two-resource multidimensional scheduling instance. -/
noncomputable def multidim_opt2 (I : MultidimInstance2) : ℝ :=
  sInf { s | ∃ (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ), multidim_is_feasible_schedule2 I x C ∧ s = ∑ j, C j }
