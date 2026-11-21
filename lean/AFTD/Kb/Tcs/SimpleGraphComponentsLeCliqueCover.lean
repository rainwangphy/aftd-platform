import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_components_le_clique_cover

Topic: graphs   Node: 1fb1c4d36c83

Provenance: helper lemma. OP-1957: component bound for a clique cover.

If the vertices of a finite graph are covered by m cliques, then the graph has at most m connected components.
-/

theorem simple_graph_components_le_clique_cover
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (T : Fin m → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ T i)
    (hclique : ∀ i, ∀ u ∈ T i, ∀ v ∈ T i, u ≠ v → G.Adj u v) :
    Nat.card G.ConnectedComponent ≤ m := by
  classical
  have hex : ∀ c : G.ConnectedComponent, ∃ i, ∃ v ∈ T i, v ∈ c.supp := by
    intro c
    obtain ⟨v,hv⟩ := c.nonempty_supp
    obtain ⟨i,hi⟩ := hcover v
    exact ⟨i,v,hi,hv⟩
  let f : G.ConnectedComponent → Fin m := fun c => Classical.choose (hex c)
  have hf (c : G.ConnectedComponent) : ∃ v ∈ T (f c), v ∈ c.supp :=
    Classical.choose_spec (hex c)
  have hinj : Function.Injective f := by
    intro c d hcd
    obtain ⟨v,hvT,hvc⟩ := hf c
    obtain ⟨w,hwT,hwd⟩ := hf d
    have hwT' : w ∈ T (f c) := by rw [hcd]; exact hwT
    have hreach : G.Reachable v w := by
      by_cases h : v = w
      · subst w
        exact SimpleGraph.Reachable.rfl
      · exact (hclique (f c) v hvT w hwT' h).reachable
    have heq : G.connectedComponentMk v = G.connectedComponentMk w :=
      SimpleGraph.ConnectedComponent.eq.mpr hreach
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hvc hwd
    exact hvc.symm.trans (heq.trans hwd)
  have h := Nat.card_le_card_of_injective f hinj
  simpa using h
