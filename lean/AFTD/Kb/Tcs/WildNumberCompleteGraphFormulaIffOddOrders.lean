import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteEvenEqOfPrecedingOdd
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_number_complete_graph_formula_iff_odd_orders

Topic: graphs   Node: cafebd2614ba

Provenance: helper lemma. General parity reduction for the OP-306 campaign, related to arXiv:2610.22142 Section3.3.3 and the existing deleted-vertex partition-lifting proof. This is a conditional transfer and equivalence, not an assertion that the unresolved odd-order cases hold.

The wild-number sharpness conjecture for minimum proper colorings of every complete graph of order at least three is equivalent to its restriction to odd orders at least three.
-/

open scoped Classical
set_option maxHeartbeats 1000000

theorem wild_number_complete_graph_formula_iff_odd_orders :
    (∀ (n k : ℕ), 3 ≤ n →
      (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k →
      ∀ c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k),
        simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4*((n+1)/2)/3) ↔
    (∀ (n k : ℕ), 3 ≤ n → n%2=1 →
      (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k →
      ∀ c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k),
        simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4*((n+1)/2)/3) := by
  constructor
  · intro h n k hn _ hk c
    exact h n k hn hk c
  · intro h n k hn hk c
    by_cases hodd : n%2=1
    · exact h n k hn hodd hk c
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      have hm : 3 ≤ m := by omega
      have hmOdd : m%2=1 := by omega
      have hsharp : ∀ cc : (⊤ : SimpleGraph (Fin m)).lineGraph.Coloring (Fin m),
          simple_graph_wild_number (⊤ : SimpleGraph (Fin m)) cc = 4*((m+1)/2)/3 := by
        intro cc
        exact h m m hm hmOdd (complete_graph_odd_line_graph_chromatic_number_eq m hm hmOdd) cc
      exact wild_number_complete_even_eq_of_preceding_odd m k hm hmOdd hsharp hk c
