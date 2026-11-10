import AFTD.Prelude
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy

/-!
# HasWinningStrategyInMem

Topic: automata   Node: beb96003f413

Provenance: formalization of a published result. Source: arXiv:2611.10136, Def. 18 and Sec. 5.1

The proposition HasWinningStrategyInMem G m_bound asserts that for a prioritized Borel game G with state space Q and k priorities, there exists a player pl : BorelGamePlayer and a finite memory type M with Fintype.card M ≤ m_bound, having a strategy strat : FiniteMemoryStrategy G pl M such that for every valid play (an infinite sequence of edges starting at ([], G.init_state) with matching consecutive source and target nodes and states) consistent with strat, pl wins: if pl = Eve, the branch traced by the play belongs to the winning set G.winning_sets p for the maximal priority p : Fin k occurring infinitely often; if pl = Adam, this condition fails.
-/

/-- Predicate that a prioritized Borel game has a winning strategy with at most m_bound memory states. -/
def HasWinningStrategyInMem {Q : Type*} {k : ℕ} (G : PrioritizedBorelGame Q k) (m_bound : ℕ) : Prop := ∃ (pl : BorelGamePlayer) (M : Type) (_ : Fintype M),
    Fintype.card M ≤ m_bound ∧
    ∃ strat : FiniteMemoryStrategy G pl M,
      ∀ play : ℕ → TreeGameEdge Q k,
        (∀ n, play n ∈ G.edges) →
        (play 0).source_node = [] ∧ (play 0).source_state = G.init_state →
        (∀ n, (play (n + 1)).source_node = (play n).source_node ++ [(play n).dir] ∧
              (play (n + 1)).source_state = (play n).target_state) →
        (∃ mem : ℕ → M, mem 0 = strat.init_mem ∧
          (∀ n, mem (n + 1) = strat.update (mem n) (play n)) ∧
          (∀ n, G.owner ((play n).source_node, (play n).source_state) = pl →
            play n = strat.choice (mem n) (play n).source_node (play n).source_state)) →
        match pl with
        | BorelGamePlayer.Eve =>
            ∃ p : Fin k,
              (Filter.Frequently (fun n => (play n).prio = p) Filter.atTop) ∧
              (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (play n).prio = q) Filter.atTop) ∧
              (fun n => (play n).dir) ∈ G.winning_sets p
        | BorelGamePlayer.Adam =>
            ¬ ∃ p : Fin k,
              (Filter.Frequently (fun n => (play n).prio = p) Filter.atTop) ∧
              (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (play n).prio = q) Filter.atTop) ∧
              (fun n => (play n).dir) ∈ G.winning_sets p
