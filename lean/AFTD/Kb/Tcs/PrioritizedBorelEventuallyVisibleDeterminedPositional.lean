import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelStrategyWins
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelFiniteHiddenOpponentChoicesPositional

/-!
# prioritized_borel_eventually_visible_determined_positional

Topic: automata   Node: 3e1f056bbe79

Provenance: original. Related work: Eventual visible-choice reduction related to arXiv:2611.10136, Conjecture 19.

A determined prioritized tree game has a memoryless winner if, along every legal play, all but finitely many moves are uniquely determined by the current position and public branch direction. This permits infinitely many visible choices and makes no finite-state or uniform hidden-choice-bound assumption.
-/

theorem prioritized_borel_eventually_visible_determined_positional {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (hdet : ∃ (pl : BorelGamePlayer) (M : Type) (σ : FiniteMemoryStrategy G pl M), PrioritizedBorelStrategyWins G pl σ) (hvisible : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) → (π 0).source_node = [] ∧ (π 0).source_state = G.init_state → (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) → ∃ N, ∀ n ≥ N, ∀ e ∈ G.edges, e.source_node = (π n).source_node → e.source_state = (π n).source_state → e.dir = (π n).dir → e = π n) : HasWinningStrategyInMem G 1 := by
  obtain ⟨pl, M, σ, hwin⟩ := hdet
  have hfinite : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) →
      (π 0).source_node = [] ∧ (π 0).source_state = G.init_state →
      (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧
        (π (n+1)).source_state = (π n).target_state) →
      ∃ N, ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨
        ∀ e ∈ G.edges, e.source_node = (π n).source_node →
          e.source_state = (π n).source_state → e.dir = (π n).dir → e = π n := by
    intro π he hi hn
    obtain ⟨N, hN⟩ := hvisible π he hi hn
    exact ⟨N, fun n hn => Or.inr (hN n hn)⟩
  obtain ⟨τ, hτ⟩ :=
    prioritized_borel_finite_hidden_opponent_choices_positional G pl M σ hwin hfinite
  exact ⟨pl, Unit, inferInstance, by simp, τ, hτ⟩
