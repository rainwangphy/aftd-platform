import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# PrioritizedBorelStrategyHistory

Topic: automata   Node: 074b512d9599

Provenance: helper lemma. arXiv:2611.10136, Definitions 18 and 19; finite histories consistent with a given strategy

An encoded finite history follows legal edges from the initial position and agrees with the chosen strategy at its player's positions. Each code entry records the direction, target state, and priority, while the indices record the current memory, public node, and game state.
-/

inductive PrioritizedBorelStrategyHistory {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) {M : Type} (σ : FiniteMemoryStrategy G pl M) : List (Bool × Q × Fin k) → M → List Bool → Q → Prop
  | root : PrioritizedBorelStrategyHistory G pl σ [] σ.init_mem [] G.init_state
  | step {h m v q} (e : TreeGameEdge Q k) : PrioritizedBorelStrategyHistory G pl σ h m v q → e ∈ G.edges → e.source_node = v → e.source_state = q → (G.owner (v, q) = pl → e = σ.choice m v q) → PrioritizedBorelStrategyHistory G pl σ (h ++ [(e.dir, e.target_state, e.prio)]) (σ.update m e) (v ++ [e.dir]) e.target_state
