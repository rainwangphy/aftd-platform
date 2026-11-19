import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGamePeelSeq
import AFTD.Kb.Tcs.ParityGameEvenWinsPlay
import AFTD.Kb.Tcs.ParityGameAttractor
import AFTD.Kb.Tcs.ParityGameAprime

/-!
# parity_game_peel_claimed_dominion_counterexample

Topic: automata   Node: c221b0ca47d2

Provenance: erratum. Corrects: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Theorem 2 (A(G, d) is a dominion of the player of d), and with it Theorems 5 and 8 (Algorithm 1 solves parity games): false on a 4-vertex game without self-loops. Definitions taken from the paper's LaTeX source (v1, the only version); the result holds under both readings of U_{k-1} at k = 0.

Consider the parity game on the four vertices 0, 1, 2, 3 in which Even owns vertices 0 and 1, Odd owns vertices 2 and 3, the priorities are 4, 0, 3, 4 (in this order), and the edges are 0→3, 1→2, 2→0, 2→1, 3→0, 3→1 (no self-loops, every vertex has a successor), with the min-parity winning condition, and take d = 3 (the priority of vertex 2, a priority of player Odd). Then (1) for every k, the set A^k(G, 3) of arXiv:2511.03752 (the second component of parity_game_peel_seq at index k, computed with own, edge and priority maps of this game and d = 3) is the set of all four vertices, so their intersection A(G, 3) is the whole vertex set; and (2) every infinite sequence of vertices that follows the edges of the game (every play, whatever the two players do) is won by Even: the least priority occurring infinitely often along it is even. So A(G, 3) is not a dominion of player Odd, who wins from no vertex, contrary to Theorem 2 of arXiv:2511.03752; and Algorithm 1 of that paper, whose first iteration on this game has maximum priority 4, hence computes A(G, 3) for Odd and assigns all of it to Odd's winning set, returns W_Odd = V although Even wins from every vertex, contrary to its Theorems 5 and 8.
-/

theorem parity_game_peel_claimed_dominion_counterexample :
    (∀ k, (parity_game_peel_seq (![true, true, false, false] : Fin 4 → Bool)
        (fun v w => (![![false, false, false, true], ![false, false, true, false],
          ![true, true, false, false], ![true, true, false, false]] : Fin 4 → Fin 4 → Bool) v w)
        (![4, 0, 3, 4] : Fin 4 → ℕ) 3 k).2 = Finset.univ) ∧
    ∀ π : ℕ → Fin 4,
      (∀ n, (![![false, false, false, true], ![false, false, true, false],
          ![true, true, false, false], ![true, true, false, false]] : Fin 4 → Fin 4 → Bool)
            (π n) (π (n + 1)) = true) →
      parity_game_even_wins_play (![4, 0, 3, 4] : Fin 4 → ℕ) π := by
  refine ⟨?_, ?_⟩
  · have h : ∀ k, parity_game_peel_seq (![true, true, false, false] : Fin 4 → Bool)
        (fun v w => (![![false, false, false, true], ![false, false, true, false],
          ![true, true, false, false], ![true, true, false, false]] : Fin 4 → Fin 4 → Bool) v w)
        (![4, 0, 3, 4] : Fin 4 → ℕ) 3 k = ({2}, Finset.univ) := by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        rw [parity_game_peel_seq, ih]
        decide
    intro k
    rw [h k]
  · intro π hπ
    by_cases h : ∀ N, ∃ n, N ≤ n ∧ π n = 1
    · refine ⟨0, rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      intro N
      obtain ⟨n, hn, e⟩ := h N
      exact ⟨n, hn, by rw [e]; rfl⟩
    · simp only [not_forall, not_exists, not_and] at h
      obtain ⟨N, hN⟩ := h
      have key : ∀ n, N + 1 ≤ n → (![4, 0, 3, 4] : Fin 4 → ℕ) (π n) = 4 := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have h1 := hN m (by omega)
        have h2 := hN (m + 1) (by omega)
        have h3 := hπ m
        generalize π m = a at h1 h3
        generalize π (m + 1) = b at h2 h3 ⊢
        revert a b
        decide
      refine ⟨4, rfl, fun M => ⟨max M (N + 1), le_max_left _ _, key _ (le_max_right _ _)⟩, ?_⟩
      intro j hj
      exact ⟨N + 1, fun n hn e => by rw [key n hn] at e; omega⟩
