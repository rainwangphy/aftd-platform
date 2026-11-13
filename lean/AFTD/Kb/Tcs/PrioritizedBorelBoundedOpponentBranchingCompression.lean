import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.PrioritizedBorelStrategyWins
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelRecordReplay
import AFTD.Kb.Tcs.PrioritizedBorelRecordInjective
import AFTD.Kb.Tcs.PrioritizedBorelOutgoingEdgeCardBound
import AFTD.Kb.Tcs.PrioritizedBorelFiniteHiddenOpponentChoicesPositional

/-!
# prioritized_borel_bounded_opponent_branching_compression

Topic: automata   Node: f970d07cacc5

Provenance: original. Related work: Bounded-adversary-branching strategy compression related to arXiv:2611.10136, Conjecture 19.

Fix a winning strategy, possibly using infinite memory, in a finite-state prioritized tree game with k priorities. If along every legal play the opponent has a genuine choice at at most d positions, then the same player has a winning strategy with at most (2k|Q|+1)^d memory states. This construction does not use Borel determinacy and works for any branch-winning sets.
-/

theorem prioritized_borel_bounded_opponent_branching_compression {Q : Type} [Fintype Q] {k : ℕ} (G : PrioritizedBorelGame Q k) (pl : BorelGamePlayer) (M : Type) (σ : FiniteMemoryStrategy G pl M) (hwin : PrioritizedBorelStrategyWins G pl σ) (d : ℕ) (hbounded : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) → (π 0).source_node = [] ∧ (π 0).source_state = G.init_state → (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) → ∀ N, Set.ncard {j : ℕ | j < N ∧ G.owner ((π j).source_node, (π j).source_state) ≠ pl ∧ ∃ e ∈ G.edges, e.source_node = (π j).source_node ∧ e.source_state = (π j).source_state ∧ e ≠ π j} ≤ d) : ∃ (M' : Type) (_ : Fintype M'), Fintype.card M' ≤ (2 * k * Fintype.card Q + 1) ^ d ∧ ∃ τ : FiniteMemoryStrategy G pl M', PrioritizedBorelStrategyWins G pl τ := by
  classical
  have hfinite : ∀ π : ℕ → TreeGameEdge Q k, (∀ n, π n ∈ G.edges) → (π 0).source_node = [] ∧ (π 0).source_state = G.init_state → (∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) → ∃ N, ∀ n ≥ N, G.owner ((π n).source_node, (π n).source_state) = pl ∨ ∀ e ∈ G.edges, e.source_node = (π n).source_node → e.source_state = (π n).source_state → e.dir = (π n).dir → e = π n := by
    intro π h1 h2 h3
    let S := {j : ℕ | G.owner ((π j).source_node, (π j).source_state) ≠ pl ∧ ∃ e ∈ G.edges, e.source_node = (π j).source_node ∧ e.source_state = (π j).source_state ∧ e ≠ π j}
    have hS : ∀ N, Set.ncard {j : ℕ | j < N ∧ j ∈ S} ≤ d := by
      intro N
      have : {j : ℕ | j < N ∧ j ∈ S} = {j : ℕ | j < N ∧ G.owner ((π j).source_node, (π j).source_state) ≠ pl ∧ ∃ e ∈ G.edges, e.source_node = (π j).source_node ∧ e.source_state = (π j).source_state ∧ e ≠ π j} := by
        ext j; simp [S]
      rw [this]
      exact hbounded π h1 h2 h3 N
    have hN_ex : ∃ N, ∀ n ≥ N, n ∉ S := by
      by_contra hc
      have hinf : S.Infinite := by
        intro hfin
        have hb := hfin.bddAbove
        obtain ⟨B, hB⟩ := hb
        apply hc
        refine ⟨B + 1, ?_⟩
        intro n hn hnS
        have := hB hnS
        omega
      obtain ⟨t, htS, htcard⟩ := hinf.exists_subset_card_eq (d + 1)
      let N := t.sup id + 1
      have hsub : (t : Set ℕ) ⊆ {j : ℕ | j < N ∧ j ∈ S} := by
        intro x hx
        refine ⟨?_, htS hx⟩
        have : id x ≤ t.sup id := Finset.le_sup hx
        dsimp [id] at this
        omega
      have hfinN : Set.Finite {j : ℕ | j < N ∧ j ∈ S} := by
        apply Set.Finite.subset (Set.finite_Iio N)
        intro x hx
        exact hx.1
      have hcard := Set.ncard_le_ncard hsub hfinN
      rw [Set.ncard_coe_finset, htcard] at hcard
      have hN := hS N
      omega
    obtain ⟨N, hN⟩ := hN_ex
    refine ⟨N, ?_⟩
    intro n hn
    have hnot := hN n hn
    dsimp [S] at hnot
    by_cases ho : G.owner ((π n).source_node, (π n).source_state) = pl
    · exact Or.inl ho
    · right
      intro e he hsn hss hdir
      by_contra hne
      apply hnot
      exact ⟨ho, ⟨e, he, hsn, hss, hne⟩⟩
  obtain ⟨τ, hτ⟩ := prioritized_borel_finite_hidden_opponent_choices_positional G pl M σ hwin hfinite
  refine ⟨Unit, inferInstance, ?_, ⟨τ, hτ⟩⟩
  simp only [Fintype.card_unit]
  have : 1 ≤ 2 * k * Fintype.card Q + 1 := by omega
  exact Nat.one_le_pow d (2 * k * Fintype.card Q + 1) this
