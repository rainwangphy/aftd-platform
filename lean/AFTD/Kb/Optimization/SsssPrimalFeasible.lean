import AFTD.Prelude
import AFTD.Kb.Optimization.SsssCuts

/-!
# ssss_primal_feasible

Topic: lp_duality   Node: 92f86062f3ff

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

For a finite vertex set V with decidable equality, a set of directed edges E : Finset (V × V), terminals s, t ∈ V, and an integer k : ℕ, a flow vector x : V × V → ℝ is feasible for the LP relaxation (SSSS-P) if: (1) x(e) ≥ 0 for all e ∈ E; (2) for every vertex v ∈ V, the net inflow (sum of x(e) for e ∈ E entering v minus sum of x(e) for e ∈ E leaving v) equals -k if v = s, k if v = t, and 0 otherwise; and (3) for every non-empty subset U ⊆ V \ {s, t}, the sum of x(e) over all edges e ∈ E crossing U in either direction (having exactly one endpoint in U, i.e. (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.1 ∉ U ∧ e.2 ∈ U)) is at least 2.
-/

/-- Primal feasibility for the Single-Source Single-Sink Multi-Path LP relaxation (SSSS-P). -/
def ssss_primal_feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (s t : V) (k : ℕ) (x : V × V → ℝ) : Prop :=
  (∀ e ∈ E, 0 ≤ x e) ∧
  (∀ v : V,
    (∑ e ∈ E.filter (fun e => e.2 = v), x e) - (∑ e ∈ E.filter (fun e => e.1 = v), x e) =
      if v = s then - (k : ℝ) else if v = t then (k : ℝ) else 0) ∧
  (∀ U ∈ ssss_cuts s t,
    2 ≤ ∑ e ∈ E.filter (fun e => (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.1 ∉ U ∧ e.2 ∈ U)), x e)
