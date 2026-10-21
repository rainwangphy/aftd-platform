import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.CubicPaleyGraph
import AFTD.Kb.Tcs.CubicPaleyGraphDecidableAdj
import AFTD.Kb.Tcs.LeSimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumberLeMaxDegreeOrHalf
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# cubic_paley_graph_zmod_thirty_one_achromatic_number

Topic: graphs   Node: e116bc6c7b26

Provenance: original. Related work: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs): the paper's bounds (q+2)/3 ≤ χ_a(G_3(q)) ≤ (q−1)/2; exact value at q = 31, found by computation (experiment 2314).

The cubic Paley graph G_3(31) has achromatic number 15 = (31 − 1)/2, the upper bound, above the value (31 + 2)/3 = 11 conjectured for large q.
-/

def cubic_paley_graph_zmod_thirty_one_achromatic_number_val : ZMod 31 → Fin 15 :=
  ![(0:Fin 15), 5, 1, 12, 10, 7, 3, 1, 8, 0, 14, 13, 5, 10, 4, 11, 12, 3, 9, 6, 14, 13, 0, 7, 2, 4, 8, 9, 11, 2, 6]

lemma cubic_paley_graph_zmod_thirty_one_achromatic_number_proper :
    ∀ {v w : ZMod 31}, (cubic_paley_graph (ZMod 31)).Adj v w →
      cubic_paley_graph_zmod_thirty_one_achromatic_number_val v ≠
        cubic_paley_graph_zmod_thirty_one_achromatic_number_val w := by
  decide +kernel

def cubic_paley_graph_zmod_thirty_one_achromatic_number_coloring :
    (cubic_paley_graph (ZMod 31)).Coloring (Fin 15) :=
  SimpleGraph.Coloring.mk
    cubic_paley_graph_zmod_thirty_one_achromatic_number_val
    cubic_paley_graph_zmod_thirty_one_achromatic_number_proper

lemma cubic_paley_graph_zmod_thirty_one_achromatic_number_achromatic :
    simple_graph_coloring_is_achromatic
      cubic_paley_graph_zmod_thirty_one_achromatic_number_coloring := by
  dsimp [simple_graph_coloring_is_achromatic]
  constructor <;> decide +kernel

lemma cubic_paley_graph_zmod_thirty_one_achromatic_number_maxDegree_le :
    (cubic_paley_graph (ZMod 31)).maxDegree ≤ 10 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  decide +kernel

theorem cubic_paley_graph_zmod_thirty_one_achromatic_number :
    simple_graph_achromatic_number (cubic_paley_graph (ZMod 31)) = 15 := by
  have h_lower : 15 ≤ simple_graph_achromatic_number (cubic_paley_graph (ZMod 31)) :=
    le_simple_graph_achromatic_number
      cubic_paley_graph_zmod_thirty_one_achromatic_number_coloring
      cubic_paley_graph_zmod_thirty_one_achromatic_number_achromatic
  have h_upper := simple_graph_achromatic_number_le_max_degree_or_half (cubic_paley_graph (ZMod 31))
  have h_deg := cubic_paley_graph_zmod_thirty_one_achromatic_number_maxDegree_le
  have h_card : Fintype.card (ZMod 31) / 2 = 15 := by decide
  omega
