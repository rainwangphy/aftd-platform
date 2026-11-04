import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreeIndependentNeighborhoodMatching

/-!
# simple_graph_triangle_free_private_neighborhood_neighbor_unique

Topic: combinatorics   Node: 14c8e9b8dffa

Provenance: helper lemma. Private-neighbor obstruction for OP-926, derived from neighborhood matching.

In a finite triangle-free graph with no independent k-set, if v has degree k − 1 and vertices x and y both have w as their only neighbor in the neighborhood of v, then x and y are equal.
-/

theorem simple_graph_triangle_free_private_neighborhood_neighbor_unique {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ)
    (htri : G.CliqueFree 3) (hfree : Gᶜ.CliqueFree k)
    (v w x y : α) (hdegree : G.degree v + 1 = k)
    (hvw : G.Adj v w) (hwx : G.Adj w x) (hwy : G.Adj w y)
    (hx : ∀ z, G.Adj v z → G.Adj z x → z = w)
    (hy : ∀ z, G.Adj v z → G.Adj z y → z = w) : x = y := by
  classical
  by_contra hne
  have hvx : ¬ G.Adj v x := by
    intro h
    exact htri {v, w, x} (SimpleGraph.is3Clique_iff.mpr ⟨v, w, x, hvw, h, hwx, rfl⟩)
  have hvy : ¬ G.Adj v y := by
    intro h
    exact htri {v, w, y} (SimpleGraph.is3Clique_iff.mpr ⟨v, w, y, hvw, h, hwy, rfl⟩)
  have hxy : ¬ G.Adj x y := by
    intro h
    exact htri {w, x, y} (SimpleGraph.is3Clique_iff.mpr ⟨w, x, y, hwx, hwy, h, rfl⟩)
  let s : Finset α := {x, y}
  have hs_ind : G.IsIndepSet (↑s : Set α) := by
    intro a ha b hb hab
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxy
    · exact fun h => hxy h.symm
    · exact absurd rfl hab
  have hs_ns : ∀ z ∈ s, ¬ G.Adj v z := by
    intro z hz
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hvx
    · exact hvy
  obtain ⟨f, hf, hfv⟩ := simple_graph_triangle_free_independent_neighborhood_matching G k htri hfree v hdegree s hs_ind hs_ns
  let a : {z // z ∈ s} := ⟨x, by simp [s]⟩
  let b : {z // z ∈ s} := ⟨y, by simp [s]⟩
  have hfx : f a = w := by
    obtain ⟨h1, h2⟩ := hfv a
    exact hx (f a) h1 h2
  have hfy : f b = w := by
    obtain ⟨h1, h2⟩ := hfv b
    exact hy (f b) h1 h2
  have heq : a = b := hf (by rw [hfx, hfy])
  have hval : (a : α) = (b : α) := congrArg Subtype.val heq
  exact hne hval
