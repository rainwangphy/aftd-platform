import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeCompl
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_compl_regular_triangle_distinct

Topic: graphs   Node: 5b1424dbe4f7

Provenance: formalization of a published result. Source: arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Lemma 2.1 (consequence); follows from the complement formula simple_graph_triangle_degree_compl.

If G is an r-regular triangle-distinct graph on N vertices, its complement is an (N − r − 1)-regular triangle-distinct graph.
-/

theorem simple_graph_compl_regular_triangle_distinct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r N : ℕ) (hN : Fintype.card V = N)
    (hreg : G.IsRegularOfDegree r) (htd : simple_graph_is_triangle_distinct G) :
    Gᶜ.IsRegularOfDegree (N - r - 1) ∧ simple_graph_is_triangle_distinct Gᶜ := by
  refine ⟨?_, ?_⟩
  · have h := hreg.compl
    rw [hN] at h
    have e : N - 1 - r = N - r - 1 := by omega
    rwa [e] at h
  · intro x y hxy
    apply htd
    have h1 := simple_graph_triangle_degree_compl G r N hN hreg x
    have h2 := simple_graph_triangle_degree_compl G r N hN hreg y
    have : (simple_graph_triangle_degree G x : ℚ) = simple_graph_triangle_degree G y := by
      rw [hxy] at h1; linarith
    exact_mod_cast this
