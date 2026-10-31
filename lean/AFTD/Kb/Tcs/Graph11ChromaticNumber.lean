import AFTD.Prelude
import AFTD.Kb.Tcs.Graph11

/-!
# graph_11_chromatic_number

Topic: graphs   Node: 515422c8db09

Provenance: formalization of a published result. Source: arXiv:2610.39430 Lemma 3.3

The chromatic number of the simple graph G_11 equals 3.
-/

/-- The chromatic number of G_11 is 3. -/
theorem graph_11_chromatic_number : graph_11.chromaticNumber = 3 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the three classes {4,5,6,7}, {0,2,8,9}, {1,3,10} form a 3-coloring
    refine SimpleGraph.Colorable.chromaticNumber_le
      (show graph_11.Colorable 3 from ?_)
    refine ⟨SimpleGraph.Coloring.mk (fun v : Fin 11 => ![1, 2, 1, 2, 0, 0, 0, 0, 1, 1, 2] v) ?_⟩
    intro v w h
    fin_cases v <;> fin_cases w <;> simp [graph_11, SimpleGraph.fromRel] at h ⊢
  · -- lower bound: {4, 8, 10} is a triangle
    exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (by simp) (fun i : Fin 3 => ![4, 8, 10] i) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [graph_11, SimpleGraph.fromRel])
