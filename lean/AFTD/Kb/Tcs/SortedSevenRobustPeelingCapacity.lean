import AFTD.Prelude

/-!
# sorted_seven_robust_peeling_capacity

Topic: graphs   Node: edf519fd3d50

Provenance: helper lemma. Finite arithmetic for the robust peeling step in the OP-110 campaign; experiment 12598.

Seven decreasing nonnegative counts satisfying the five displayed robust-peeling alternatives have sum at least twenty.
-/

theorem sorted_seven_robust_peeling_capacity
    (d : Fin 7 → ℕ)
    (hs : ∀ i j, i ≤ j → d j ≤ d i)
    (h0 : 6 ≤ d 0 ∨ 5 ≤ d 2)
    (h1 : 5 ≤ d 1 ∨ 4 ≤ d 3)
    (h2 : 4 ≤ d 2 ∨ 3 ≤ d 4)
    (h3 : 3 ≤ d 3 ∨ 2 ≤ d 5)
    (h4 : 2 ≤ d 4 ∨ 1 ≤ d 6) :
    20 ≤ ∑ i : Fin 7, d i := by
  have hs01 := hs 0 1 (by decide)
  have hs12 := hs 1 2 (by decide)
  have hs23 := hs 2 3 (by decide)
  have hs34 := hs 3 4 (by decide)
  have hs45 := hs 4 5 (by decide)
  have hs56 := hs 5 6 (by decide)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change 20 ≤ d 0 + (d 1 + (d 2 + (d 3 + (d 4 + (d 5 + (d 6 + 0))))))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> omega
