import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# enc1385Follow

Topic: automata   Node: afd839611d8e

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

Starting with a phase-game memory and position, follow a fixed strategy for a specified number of phase steps, returning the resulting memory and position.
-/

noncomputable def enc1385Follow {Q M : Type} [Fintype Q]
    (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer)
    (σ : FiniteMemoryStrategy (enc1385Game G) pl M)
    (m : M) (node : List Bool) (s : Enc1385State Q) :
    ℕ → M × List Bool × Enc1385State Q
  | 0 => (m, node, s)
  | n + 1 =>
      let st := enc1385Follow G pl σ m node s n
      let e := σ.choice st.1 st.2.1 st.2.2
      (σ.update st.1 e, st.2.1 ++ [e.dir], e.target_state)
