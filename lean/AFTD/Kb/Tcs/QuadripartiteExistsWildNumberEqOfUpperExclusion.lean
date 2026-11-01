import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsSealFreePartition
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumberAttained

/-!
# quadripartite_exists_wild_number_eq_of_upper_exclusion

Topic: graphs   Node: a97a5614b87c

Provenance: helper lemma. step towards quadripartite_minimum_coloring_max_wild_number_eq

If every proper 3n-edge-colouring of K_{n,n,n,n} has wild number at most 2n + 1, and some colouring has no colour-connecting set of at most 2n edges, then that colouring has wild number exactly 2n + 1.
-/

/-- The exclusion form of sharpness plus the universal upper bound yields an attaining colouring. -/
theorem quadripartite_exists_wild_number_eq_of_upper_exclusion (n : ℕ) (hn : 3 ≤ n)
    (hU : ∀ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
      simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c ≤ 2 * n + 1)
    (hE : ∃ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
      ∀ W : Finset (Sym2 (Fin 4 × Fin n)), W.card ≤ 2 * n →
        ¬ simple_graph_is_color_connecting (SimpleGraph.completeEquipartiteGraph 4 n) c ↑W) :
    ∃ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
      simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c = 2 * n + 1 := by
  let G := SimpleGraph.completeEquipartiteGraph 4 n
  have hconn : G.Connected := by
    have : Nonempty (Fin 4 × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    refine ⟨fun u v => ?_⟩
    by_cases h : u.1 = v.1
    · obtain ⟨i, hi⟩ : ∃ i : Fin 4, i ≠ u.1 := by
        by_contra! hcontra
        have h0 := hcontra ⟨0, by omega⟩
        have h1 := hcontra ⟨1, by omega⟩
        have : (⟨0, by omega⟩ : Fin 4) = ⟨1, by omega⟩ := h0.trans h1.symm
        have : (0 : ℕ) = 1 := congr_arg Fin.val this
        omega
      let w : Fin 4 × Fin n := (i, ⟨0, by omega⟩)
      have huw : G.Adj u w := by
        rw [SimpleGraph.completeEquipartiteGraph_adj]
        exact hi.symm
      have hwv : G.Adj w v := by
        rw [SimpleGraph.completeEquipartiteGraph_adj]
        rw [← h]
        exact hi
      exact (huw.reachable).trans hwv.reachable
    · have hadj : G.Adj u v := by
        rw [SimpleGraph.completeEquipartiteGraph_adj]
        exact h
      exact hadj.reachable
  obtain ⟨c, hc⟩ := hE
  use c
  have hu := hU c
  obtain ⟨W, hWcard, hWconn⟩ := simple_graph_wild_number_attained G c hconn
  have hnotle : ¬ W.card ≤ 2 * n := by
    intro hle
    exact hc W hle hWconn
  have hgt : 2 * n + 1 ≤ simple_graph_wild_number G c := by
    rw [← hWcard]
    omega
  exact le_antisymm hu hgt
