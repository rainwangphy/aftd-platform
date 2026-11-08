import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance

/-!
# multidim_is_feasible_schedule

Topic: online_algorithms   Node: 36788e8bdd6f

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.1

A rate allocation x and completion time vector C satisfy multidim_is_feasible_schedule I x C for an instance I with D resources if for every job j and time t, 0 ≤ x j t ≤ I.u j; for every resource d and nonnegative time t ≥ 0, the total resource demand ∑ j, I.a j d * x j t ≤ 1; and for every job j, 0 ≤ C j, x j is interval integrable with respect to the volume measure on [0, C j], and the interval integral of x j from 0 to C j equals I.p j.
-/

/-- Feasibility predicate for a multidimensional scheduling rate allocation and completion times. -/
def multidim_is_feasible_schedule {D : ℕ} (I : MultidimInstance D) (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ) : Prop :=
  (∀ j t, 0 ≤ x j t ∧ x j t ≤ I.u j) ∧
  (∀ (d : Fin D) (t : ℝ), 0 ≤ t → ∑ j : Fin I.n, I.a j d * x j t ≤ 1) ∧
  (∀ j, 0 ≤ C j ∧ IntervalIntegrable (x j) MeasureTheory.volume 0 (C j) ∧ ∫ t in (0 : ℝ)..(C j), x j t = I.p j)
