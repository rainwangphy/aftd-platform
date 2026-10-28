import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphUpperSubFourAddParity
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_number_complete_thirteen_fourteen_eq_nine_or_ten

Topic: graphs   Node: 4934e761ad8a

Provenance: helper lemma. Finite-frontier corollary for OP-306: the new uniform upper bound is 10 at n=13,14, and arXiv:2610.22142 Theorem 3.4 gives lower bound 9. The value 9 remains conjectural universally at these orders.

For n=13 or n=14, every minimum proper edge coloring of K_n has wild number either 9 or 10.
-/

theorem wild_number_complete_thirteen_fourteen_eq_nine_or_ten (n k : ℕ) (hn : n = 13 ∨ n = 14)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 9 ∨
      simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 10 := by
  have hu := wild_number_complete_graph_upper_sub_four_add_parity n k (by rcases hn with h | h <;> omega) hk c
  have hl := wild_number_complete_graph_min_proper_coloring_ge n k (by rcases hn with h | h <;> omega) hk c
  rcases hn with rfl | rfl <;> norm_num at hu hl <;> omega
