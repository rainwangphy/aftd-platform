import AFTD.Prelude

/-!
# kuramoto_critical_coupling

Topic: classical_mechanics   Node: aa8fcf493b8a

Provenance: formalization of a published result. Source: Dekker and Taylor (2013), Synchronization Properties of Trees in the Kuramoto Model, Thm 3

The critical coupling K_H of a tree H under natural frequencies ω is the maximum over all edges e of the absolute sum of deviations (ω_v - ω_bar) over either connected component of H - e.
-/

/-- The exact critical coupling for phase locking in the Kuramoto model on a tree H with frequencies ω. -/
noncomputable def kuramoto_critical_coupling {V : Type*} [Fintype V] (H : SimpleGraph V) (ω : V → ℝ) : ℝ := by
  classical
  let mean := (∑ v : V, ω v) / Fintype.card V
  exact ⨆ (u : V) (v : V) (_ : H.Adj u v),
    |∑ w : V, if (H.deleteEdges {s(u, v)}).Reachable u w then (ω w - mean) else 0|
