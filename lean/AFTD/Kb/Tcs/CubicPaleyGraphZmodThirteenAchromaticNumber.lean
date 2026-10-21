import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.CubicPaleyGraph
import AFTD.Kb.Tcs.CubicPaleyGraphDecidableAdj
import AFTD.Kb.Tcs.LeSimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumberLeMaxDegreeOrHalf
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# cubic_paley_graph_zmod_thirteen_achromatic_number

Topic: graphs   Node: 985cfa59899a

Provenance: original. Related work: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs): the paper's bounds (q+2)/3 ≤ χ_a(G_3(q)) ≤ (q−1)/2; this is the exact value at q = 13, found by computation (experiment 2294).

The cubic Paley graph G_3(13) has achromatic number 6 = (13 − 1)/2, the upper bound, above the value (13 + 2)/3 = 5 conjectured for large q.
-/

def cubic_paley_graph_zmod_thirteen_achromatic_number_val : ZMod 13 → Fin 6 :=
  ![(0:Fin 6), 3, 2, 3, 4, 2, 1, 5, 4, 2, 0, 5, 1]

lemma cubic_paley_graph_zmod_thirteen_achromatic_number_proper :
    ∀ {v w : ZMod 13}, (cubic_paley_graph (ZMod 13)).Adj v w →
      cubic_paley_graph_zmod_thirteen_achromatic_number_val v ≠
        cubic_paley_graph_zmod_thirteen_achromatic_number_val w := by
  decide

def cubic_paley_graph_zmod_thirteen_achromatic_number_coloring :
    (cubic_paley_graph (ZMod 13)).Coloring (Fin 6) :=
  SimpleGraph.Coloring.mk
    cubic_paley_graph_zmod_thirteen_achromatic_number_val
    cubic_paley_graph_zmod_thirteen_achromatic_number_proper

lemma cubic_paley_graph_zmod_thirteen_achromatic_number_achromatic :
    simple_graph_coloring_is_achromatic
      cubic_paley_graph_zmod_thirteen_achromatic_number_coloring := by
  dsimp [simple_graph_coloring_is_achromatic]
  constructor <;> decide

lemma cubic_paley_graph_zmod_thirteen_achromatic_number_maxDegree_le :
    (cubic_paley_graph (ZMod 13)).maxDegree ≤ 4 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  decide

theorem cubic_paley_graph_zmod_thirteen_achromatic_number :
    simple_graph_achromatic_number (cubic_paley_graph (ZMod 13)) = 6 := by
  have h_lower : 6 ≤ simple_graph_achromatic_number (cubic_paley_graph (ZMod 13)) :=
    le_simple_graph_achromatic_number
      cubic_paley_graph_zmod_thirteen_achromatic_number_coloring
      cubic_paley_graph_zmod_thirteen_achromatic_number_achromatic
  have h_upper := simple_graph_achromatic_number_le_max_degree_or_half (cubic_paley_graph (ZMod 13))
  have h_deg := cubic_paley_graph_zmod_thirteen_achromatic_number_maxDegree_le
  have h_card : Fintype.card (ZMod 13) / 2 = 6 := by decide
  omega
