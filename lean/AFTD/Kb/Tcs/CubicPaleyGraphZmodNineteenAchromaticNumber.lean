import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.CubicPaleyGraph
import AFTD.Kb.Tcs.CubicPaleyGraphDecidableAdj
import AFTD.Kb.Tcs.LeSimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumberLeMaxDegreeOrHalf
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# cubic_paley_graph_zmod_nineteen_achromatic_number

Topic: graphs   Node: 06511159c87d

Provenance: original. Related work: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs): the paper's bounds (q+2)/3 ≤ χ_a(G_3(q)) ≤ (q−1)/2; this is the exact value at q = 19, found by computation (experiment 2294).

The cubic Paley graph G_3(19) has achromatic number 9 = (19 − 1)/2, the upper bound, above the value (19 + 2)/3 = 7 conjectured for large q.
-/

/-- Colour table for the achromatic 9-colouring of the cubic Paley graph on `ZMod 19`. -/
def cubic_paley_graph_zmod_nineteen_achromatic_number_color : ZMod 19 → Fin 9 :=
  ![0, 8, 3, 2, 8, 1, 0, 1, 7, 4, 7, 6, 2, 4, 8, 5, 6, 5, 3]

/-- The 9-colouring of the cubic Paley graph on `ZMod 19` given by the colour table above. -/
def cubic_paley_graph_zmod_nineteen_achromatic_number_coloring :
    (cubic_paley_graph (ZMod 19)).Coloring (Fin 9) :=
  SimpleGraph.Coloring.mk cubic_paley_graph_zmod_nineteen_achromatic_number_color (by decide)

/-- The colouring is achromatic: surjective, with an edge between every pair of classes. -/
theorem cubic_paley_graph_zmod_nineteen_achromatic_number_achromatic :
    simple_graph_coloring_is_achromatic
      cubic_paley_graph_zmod_nineteen_achromatic_number_coloring := by
  dsimp [simple_graph_coloring_is_achromatic,
    cubic_paley_graph_zmod_nineteen_achromatic_number_coloring, SimpleGraph.Coloring.mk,
    cubic_paley_graph_zmod_nineteen_achromatic_number_color]
  decide

/-- The cubic Paley graph on `ZMod 19` is 6-regular, so `max (Δ+1) ⌊19/2⌋ = 9`. -/
theorem cubic_paley_graph_zmod_nineteen_achromatic_number_max :
    max ((cubic_paley_graph (ZMod 19)).maxDegree + 1) (Fintype.card (ZMod 19) / 2) = 9 := by
  decide

theorem cubic_paley_graph_zmod_nineteen_achromatic_number :
    simple_graph_achromatic_number (cubic_paley_graph (ZMod 19)) = 9 := by
  refine le_antisymm ?_ ?_
  · have h := simple_graph_achromatic_number_le_max_degree_or_half (cubic_paley_graph (ZMod 19))
    rwa [cubic_paley_graph_zmod_nineteen_achromatic_number_max] at h
  · exact le_simple_graph_achromatic_number _ cubic_paley_graph_zmod_nineteen_achromatic_number_achromatic
