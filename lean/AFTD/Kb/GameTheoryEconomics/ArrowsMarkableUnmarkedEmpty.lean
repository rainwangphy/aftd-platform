import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsMarkableUnmarked
import AFTD.Kb.GameTheoryEconomics.TreeMarkableEdges
import AFTD.Kb.GameTheoryEconomics.ArrowsEmptyPos

/-!
# arrows_markable_unmarked_empty

Topic: combinatorial_games   Node: 2aa208390b3b

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

In the empty position the number of unmarked markable edges equals the number of markable (non-pendant) edges, tree_markable_edges.
-/

theorem arrows_markable_unmarked_empty {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    arrows_markable_unmarked G (ArrowsEmptyPos V) = tree_markable_edges G := by
  classical
  unfold arrows_markable_unmarked tree_markable_edges
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b => simp [ArrowsEmptyPos]
