import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree

/-!
# op_1355_clique_components_is_claw_free

Topic: statistical_mechanics   Node: c2147e8837f3

Provenance: helper lemma. knowledgebase

Every finite simple graph G on a finite type V with decidable equality whose connected components are all cliques is claw-free.
-/

/-- Every finite graph whose connected components are cliques is claw-free. -/
theorem op_1355_clique_components_is_claw_free
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) :
    IsClawFree G := by
  intro ⟨f⟩
  let c0 : Fin 1 ⊕ Fin 3 := Sum.inl 0
  let u : Fin 1 ⊕ Fin 3 := Sum.inr 0
  let v : Fin 1 ⊕ Fin 3 := Sum.inr 1
  have hcu : G.Adj (f c0) (f u) := by
    rw [SimpleGraph.Embedding.map_adj_iff]
    simp [c0, u, completeBipartiteGraph_adj]
  have hcv : G.Adj (f c0) (f v) := by
    rw [SimpleGraph.Embedding.map_adj_iff]
    simp [c0, v, completeBipartiteGraph_adj]
  have hnot : ¬ G.Adj (f u) (f v) := by
    rw [SimpleGraph.Embedding.map_adj_iff]
    simp [u, v, completeBipartiteGraph_adj]
  have hne : f u ≠ f v := by
    intro h
    have := f.injective h
    dsimp [u, v] at this
    cases this
  have h_comp_u : G.connectedComponentMk (f u) = G.connectedComponentMk (f c0) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hcu.symm
  have h_comp_v : G.connectedComponentMk (f v) = G.connectedComponentMk (f c0) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hcv.symm
  have h_comp : G.connectedComponentMk (f u) = G.connectedComponentMk (f v) :=
    h_comp_u.trans h_comp_v.symm
  let C := G.connectedComponentMk (f v)
  have hu_mem : f u ∈ C.supp := h_comp
  have hv_mem : f v ∈ C.supp := rfl
  have hadj : G.Adj (f u) (f v) := hclique C hu_mem hv_mem hne
  exact hnot hadj
