import AFTD.Prelude
import AFTD.Kb.Optimization.SsssCuts

/-!
# ssss_dual_feasible

Topic: lp_duality   Node: cbdf5dfeca79

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

A node potential vector a : V → ℝ and cut dual vector y : Finset V → ℝ are feasible for the dual LP relaxation (SSSS-D) on edge set E : Finset (V × V) with edge costs c : V × V → ℝ and terminals s, t ∈ V if: (1) y(U) ≥ 0 for every non-empty subset U ⊆ V \ {s, t}; and (2) for every edge e = (v, w) ∈ E, a(w) - a(v) plus the sum of y(U) over all non-empty subsets U ⊆ V \ {s, t} crossed by e in either direction (having exactly one endpoint in U, i.e. (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.1 ∉ U ∧ e.2 ∈ U)) is at most c(e).
-/

/-- Dual feasibility for the Single-Source Single-Sink Multi-Path LP relaxation (SSSS-D). -/
def ssss_dual_feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (c : V × V → ℝ) (s t : V)
    (a : V → ℝ) (y : Finset V → ℝ) : Prop :=
  (∀ U ∈ ssss_cuts s t, 0 ≤ y U) ∧
  (∀ e ∈ E,
    a e.2 - a e.1 + ∑ U ∈ (ssss_cuts s t).filter (fun U => (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.1 ∉ U ∧ e.2 ∈ U)), y U ≤ c e)
