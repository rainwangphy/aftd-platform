import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph

/-!
# simple_graph_reconfiguration_frozen_core_reachable_eq

Topic: graphs   Node: d4e6253d72b2

Provenance: formalization of a published result. Source: arXiv:2610.27527 Lemma 2.3

Let G be a simple graph, s a subset of vertices, and α a proper k-coloring of G whose restriction to the induced subgraph on s is frozen with respect to all k colors. Then every coloring β reachable from α in the k-reconfiguration graph of G agrees with α on s.
-/

/-- Every coloring reachable in the k-reconfiguration graph from a coloring that is frozen on an induced subgraph agrees with it on that subgraph. -/
theorem simple_graph_reconfiguration_frozen_core_reachable_eq
    {V : Type*} (G : SimpleGraph V) {k : ℕ} (s : Set V)
    (α β : G.Coloring (Fin k))
    (hfrozen : ∀ (x : V), x ∈ s → ∀ (i : Fin k), α x = i ∨ ∃ y ∈ s, G.Adj x y ∧ α y = i)
    (hreach : (simple_graph_reconfiguration_graph G k).Reachable α β) :
    ∀ x ∈ s, β x = α x := by
  have hstep : ∀ {c₁ c₂ : G.Coloring (Fin k)},
      (simple_graph_reconfiguration_graph G k).Adj c₁ c₂ →
      (∀ x ∈ s, c₁ x = α x) → (∀ x ∈ s, c₂ x = α x) := by
    intro c₁ c₂ hadj hc₁
    obtain ⟨v, hv, huniq⟩ := hadj
    have hv_notin_s : v ∉ s := by
      intro hvs
      have hcases := hfrozen v hvs (c₂ v)
      rcases hcases with h1 | ⟨y, hys, hadj_vy, hy_col⟩
      · rw [← hc₁ v hvs] at h1
        exact hv h1
      · have hne : y ≠ v := hadj_vy.ne'
        have hc12 : c₁ y = c₂ y := by
          by_contra hne'
          exact hne (huniq y hne')
        have hc2y : c₂ y = c₂ v := by
          calc c₂ y = c₁ y := hc12.symm
          _ = α y := hc₁ y hys
          _ = c₂ v := hy_col
        exact c₂.valid hadj_vy (hc2y.symm)
    intro x hxs
    have hxne : x ≠ v := fun h => hv_notin_s (h ▸ hxs)
    have hc12 : c₁ x = c₂ x := by
      by_contra hne'
      exact hxne (huniq x hne')
    rw [← hc12, hc₁ x hxs]
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => intro x _; rfl
  | tail _ hadj ih => exact hstep hadj ih
