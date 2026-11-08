import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance2

/-!
# multidim_is_feasible_schedule2

Topic: online_algorithms   Node: 1eea16043a5e

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.1

A rate allocation x and completion time vector C satisfy multidim_is_feasible_schedule2 I x C if for every job j and time t, 0 ≤ x j t ≤ I.u j; for every resource d and nonnegative time t ≥ 0, the total resource demand ∑ j, I.a j d * x j t ≤ 1; and for every job j, 0 ≤ C j, x j is interval integrable with respect to the volume measure on [0, C j], and the interval integral of x j from 0 to C j equals I.p j.
-/

/-- Feasibility of a schedule for a multidimensional scheduling instance with two resources. -/
def multidim_is_feasible_schedule2 (I : MultidimInstance2) (x : Fin I.n → ℝ → ℝ) (C : Fin I.n → ℝ) : Prop :=
  (∀ j t, 0 ≤ x j t ∧ x j t ≤ I.u j) ∧
  (∀ (d : Fin 2) (t : ℝ), 0 ≤ t → ∑ j : Fin I.n, I.a j d * x j t ≤ 1) ∧
  (∀ j, 0 ≤ C j ∧ IntervalIntegrable (x j) MeasureTheory.volume 0 (C j) ∧ ∫ t in (0 : ℝ)..(C j), x j t = I.p j)
