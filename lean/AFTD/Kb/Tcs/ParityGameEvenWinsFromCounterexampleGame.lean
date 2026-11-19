import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameEvenWinsFrom
import AFTD.Kb.Tcs.ParityGamePeelClaimedDominionCounterexample
import AFTD.Kb.Tcs.ParityGameEvenWinsPlay
import AFTD.Kb.Tcs.ParityGamePeelSeq

/-!
# parity_game_even_wins_from_counterexample_game

Topic: automata   Node: 7f05422bec83

Provenance: helper lemma. arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time): sanity lemma for the positional winning definition, on the counterexample game to Theorem 2

In the parity game on the four vertices 0, 1, 2, 3 in which Even owns vertices 0 and 1, Odd owns vertices 2 and 3, the priorities are 4, 0, 3, 4 (in this order), and the edges are 0→3, 1→2, 2→0, 2→1, 3→0, 3→1 (no self-loops, every vertex has a successor), Even wins from every vertex v with a positional strategy (min-parity condition).
-/

theorem parity_game_even_wins_from_counterexample_game (v : Fin 4) :
    parity_game_even_wins_from (![true, true, false, false] : Fin 4 → Bool)
        (fun v w => (![![false, false, false, true], ![false, false, true, false],
          ![true, true, false, false], ![true, true, false, false]] : Fin 4 → Fin 4 → Bool) v w)
        (![4, 0, 3, 4] : Fin 4 → ℕ) v := by
  refine ⟨![3, 2, 0, 0], by decide, fun π _ hπ _ => ?_⟩
  exact parity_game_peel_claimed_dominion_counterexample.2 π hπ
