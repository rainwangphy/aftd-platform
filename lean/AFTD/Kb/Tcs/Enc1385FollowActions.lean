import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385Follow
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# enc1385FollowActions

Topic: automata   Node: 52b2cb7341c0

Provenance: helper lemma. Block replay for arXiv:2611.10136, Conjecture 19.

The sequence of public bits and priorities selected by a phase-game strategy in its first n steps from a specified memory and position.
-/

noncomputable def enc1385FollowActions {Q M : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (pl : BorelGamePlayer) (σ : FiniteMemoryStrategy (enc1385Game G) pl M) (m : M) (node : List Bool) (s : Enc1385State Q) : ℕ → List (Bool × Fin 3)
| 0 => []
| n + 1 => let st := enc1385Follow G pl σ m node s n; let e := σ.choice st.1 st.2.1 st.2.2; enc1385FollowActions G pl σ m node s n ++ [(e.dir,e.prio)]
