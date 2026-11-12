import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# PrioritizedBorelStrategyWins

Topic: automata   Node: ec7f82ab3346

Provenance: helper lemma. arXiv:2611.10136, Definitions 18 and 19; arbitrary-memory strategy predicate

A strategy wins for its player if every legal play from the initial position consistent with its memory update and choices is won by that player according to the maximal recurring priority and the corresponding branch set. The memory type need not be finite.
-/

def PrioritizedBorelStrategyWins {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) {M : Type} (strat : FiniteMemoryStrategy G pl M) : Prop := ∀ play : ℕ → TreeGameEdge Q k, (∀ n, play n ∈ G.edges) → (play 0).source_node = [] ∧ (play 0).source_state = G.init_state → (∀ n, (play (n+1)).source_node = (play n).source_node ++ [(play n).dir] ∧ (play (n+1)).source_state = (play n).target_state) → (∃ mem : ℕ → M, mem 0 = strat.init_mem ∧ (∀ n, mem (n+1) = strat.update (mem n) (play n)) ∧ (∀ n, G.owner ((play n).source_node, (play n).source_state) = pl → play n = strat.choice (mem n) (play n).source_node (play n).source_state)) → match pl with | BorelGamePlayer.Eve => ∃ p : Fin k, Filter.Frequently (fun n => (play n).prio = p) Filter.atTop ∧ (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (play n).prio = q) Filter.atTop) ∧ (fun n => (play n).dir) ∈ G.winning_sets p | BorelGamePlayer.Adam => ¬ ∃ p : Fin k, Filter.Frequently (fun n => (play n).prio = p) Filter.atTop ∧ (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (play n).prio = q) Filter.atTop) ∧ (fun n => (play n).dir) ∈ G.winning_sets p
