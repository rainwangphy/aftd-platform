import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# prioritized_borel_dual_game

Topic: automata   Node: ac34871dd261

Provenance: helper lemma. arXiv:2611.10136, Definitions 18 and 19; swap the players and complement the branch sets

The dual game exchanges the owners of every position and complements each winning branch set while leaving states, edges, and priorities unchanged.
-/

def prioritized_borel_dual_game {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) : PrioritizedBorelGame Q k := { owner := fun p => match G.owner p with | BorelGamePlayer.Eve => BorelGamePlayer.Adam | BorelGamePlayer.Adam => BorelGamePlayer.Eve, init_state := G.init_state, edges := G.edges, edges_outgoing := G.edges_outgoing, winning_sets := fun i => (G.winning_sets i)ᶜ, winning_measurable := fun i => (G.winning_measurable i).compl }
