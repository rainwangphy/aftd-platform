import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRamseyProperty

/-!
# simple_graph_ramsey_property_mono

Topic: combinatorics   Node: 891695f9709a

Provenance: helper lemma. step towards book_ramsey_from_conference_graph

Let F and H be simple graphs. If the two-color Ramsey property holds on N vertices (every graph on N vertices contains F or its complement contains H), then it holds on M vertices for any M ≥ N.
-/

/-- Monotonicity of simple graph Ramsey property: if every graph on N vertices contains F or its complement contains H, the same holds for any M ≥ N. -/
theorem simple_graph_ramsey_property_mono {α β : Type*} (F : SimpleGraph α) (H : SimpleGraph β)
    {N M : ℕ} (hle : N ≤ M) (h : simple_graph_ramsey_property F H N) :
    simple_graph_ramsey_property F H M := by
  intro G
  let emb : Fin N ↪ Fin M := Fin.castLEEmb hle
  let G' : SimpleGraph (Fin N) := G.comap emb
  rcases h G' with hc | hc
  · left
    obtain ⟨c⟩ := hc
    refine ⟨⟨⟨fun x => emb (c.toHom x), ?_⟩, ?_⟩⟩
    · intro x y hxy
      have h1 := c.toHom.map_adj hxy
      rwa [SimpleGraph.comap_adj] at h1
    · exact emb.injective.comp c.injective'
  · right
    obtain ⟨c⟩ := hc
    refine ⟨⟨⟨fun x => emb (c.toHom x), ?_⟩, ?_⟩⟩
    · intro x y hxy
      have h1 := c.toHom.map_adj hxy
      rw [SimpleGraph.compl_adj] at h1 ⊢
      refine ⟨?_, ?_⟩
      · intro heq
        exact h1.1 (emb.injective heq)
      · intro h2
        exact h1.2 ((SimpleGraph.comap_adj).mpr h2)
    · exact emb.injective.comp c.injective'
