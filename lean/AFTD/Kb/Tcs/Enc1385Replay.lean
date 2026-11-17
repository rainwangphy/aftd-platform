import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385BlockMoves
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# enc1385Replay

Topic: automata   Node: 91bdf6c7f92f

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

Replay the bit-and-priority block of an original edge from a phase-game node, state, and strategy memory, returning the resulting memory, node, and phase state.
-/

noncomputable def enc1385ReplayStep {Q M : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer)
    (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (st : M × List Bool × Enc1385State Q) (a : Bool × Fin 3) :
    M × List Bool × Enc1385State Q :=
  let e : TreeGameEdge (Enc1385State Q) 3 :=
    ⟨st.2.1, st.2.2, a.1, a.2, enc1385Step G st.2.2 a.1⟩
  (σ.update st.1 e, st.2.1 ++ [a.1], e.target_state)

noncomputable def enc1385Replay {Q M : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer)
    (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node : List Bool) (s : Enc1385State Q) (e : TreeGameEdge Q 3) :
    M × List Bool × Enc1385State Q :=
  (enc1385BlockMoves e).foldl (enc1385ReplayStep G pl σ) (m, node, s)
