import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphLeSubOne
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_number_complete_three_min_proper_coloring_eq

Topic: graphs   Node: 51405a5ec7e8

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Theorem 3.5 (the exact values for 3 ≤ n ≤ 12), case n = 3; it is the case n = 3 of the Sec. 6 conjecture.

For every minimum proper edge colouring of K_3, the wild number is 2 = ⌊4⌈3/2⌉/3⌋: the case n = 3 of the conjecture in Sec. 6.
-/

theorem wild_number_complete_three_min_proper_coloring_eq (k : ℕ)
    (hk : (⊤ : SimpleGraph (Fin 3)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin 3)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin 3)) c = 2 := by
  have h1 := wild_number_complete_graph_le_sub_one 3 (by norm_num) c
  have h2 := wild_number_complete_graph_min_proper_coloring_ge 3 k (le_refl 3) hk c
  norm_num at h1 h2
  omega
