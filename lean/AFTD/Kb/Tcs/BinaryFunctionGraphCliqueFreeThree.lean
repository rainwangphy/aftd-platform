import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryFunctionGraph
import AFTD.Kb.Tcs.ColorableOfExistsIndepCover

/-!
# binary_function_graph_clique_free_three

Topic: graphs   Node: 71bad4ca52ff

Provenance: formalization of a published result. Source: arXiv:2610.37920 Lemma 2.3

If a simple graph G has chromatic number strictly greater than 6, then its binary function graph is triangle-free (3-clique free).
-/

/-- If G has chromatic number > 6, then its binary function graph is triangle-free. -/
theorem binary_function_graph_clique_free_three {V : Type*} (G : SimpleGraph V) (h : G.chromaticNumber > 6) : (binary_function_graph G).CliqueFree 3 := by
  classical
  intro t ht
  rw [SimpleGraph.isNClique_iff] at ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  have hxy_adj : (binary_function_graph G).Adj x y := hclique (x := x) (by simp) (y := y) (by simp) hxy
  have hxz_adj : (binary_function_graph G).Adj x z := hclique (x := x) (by simp) (y := z) (by simp) hxz
  have hyz_adj : (binary_function_graph G).Adj y z := hclique (x := y) (by simp) (y := z) (by simp) hyz
  let S : Fin 6 → Set V := ![{v | x v = false ∧ y v = false},
    {v | x v = true ∧ y v = true},
    {v | x v = false ∧ z v = false},
    {v | x v = true ∧ z v = true},
    {v | y v = false ∧ z v = false},
    {v | y v = true ∧ z v = true}]
  have hS_indep : ∀ i, G.IsIndepSet (S i) := by
    intro i
    fin_cases i
    · exact hxy_adj.2 false
    · exact hxy_adj.2 true
    · exact hxz_adj.2 false
    · exact hxz_adj.2 true
    · exact hyz_adj.2 false
    · exact hyz_adj.2 true
  have hS_cover : ∀ v : V, ∃ i, v ∈ S i := by
    intro v
    cases hx : x v <;> cases hy : y v <;> cases hz : z v
    · exact ⟨0, by simp [S, hx, hy]⟩
    · exact ⟨0, by simp [S, hx, hy]⟩
    · exact ⟨2, by simp [S, hx, hz]⟩
    · exact ⟨5, by simp [S, hy, hz]⟩
    · exact ⟨4, by simp [S, hy, hz]⟩
    · exact ⟨3, by simp [S, hx, hz]⟩
    · exact ⟨1, by simp [S, hx, hy]⟩
    · exact ⟨1, by simp [S, hx, hy]⟩
  have hcol : G.Colorable 6 := colorable_of_exists_indep_cover G S hS_indep hS_cover
  have hle : G.chromaticNumber ≤ (6 : ℕ∞) := hcol.chromaticNumber_le
  exact (not_le_of_gt h) hle
