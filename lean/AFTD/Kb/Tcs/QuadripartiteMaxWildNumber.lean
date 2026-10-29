import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# quadripartite_max_wild_number

Topic: graphs   Node: ecb577c3c4f6

Provenance: original. Related work: arXiv:2610.22142

The maximum wild number of the complete equipartite graph K_{n,n,n,n} over all proper edge colorings using exactly 3n colors.
-/

/-- The maximum wild number over all proper (3n)-edge colorings of K_{n,n,n,n}. -/
noncomputable def quadripartite_max_wild_number (n : ℕ) : ℕ := sSup { k : ℕ | ∃ c : (SimpleGraph.completeEquipartiteGraph 4 n).lineGraph.Coloring (Fin (3 * n)),
    simple_graph_wild_number (SimpleGraph.completeEquipartiteGraph 4 n) c = k }
