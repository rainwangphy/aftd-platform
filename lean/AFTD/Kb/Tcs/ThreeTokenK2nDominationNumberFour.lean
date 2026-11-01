import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphDominationNumber
import AFTD.Kb.Tcs.ThreeTokenK2nDominationNumberFourLe
import AFTD.Kb.Tcs.ThreeTokenK2nDominationNumberFourGe

/-!
# three_token_k2n_domination_number_four

Topic: graphs   Node: 48fae3fc9450

Provenance: original. Related work: arXiv:2610.28936, Section 5

The domination number of the 3-token graph F_3(K_{2,4}) of the complete bipartite graph K_{2,4} is 4.
-/

/-- The domination number of F_3(K_{2,4}) is 4. -/
theorem three_token_k2n_domination_number_four :
    simple_graph_domination_number (token_graph (completeBipartiteGraph (Fin 2) (Fin 4)) 3) = 4 := le_antisymm three_token_k2n_domination_number_four_le three_token_k2n_domination_number_four_ge
