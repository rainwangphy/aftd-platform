import AFTD.Prelude

/-!
# catch_up_icc_erase_nonempty

Topic: combinatorial_games   Node: 8477ad3cf37a

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

When N(N+1)/2 is even and x is in {1, ..., N}, erasing x leaves a nonempty set.
-/

/-- For any N with even triangular number and any x in {1, ..., N}, the remaining set {1, ..., N} \ {x} is nonempty. -/
theorem catch_up_icc_erase_nonempty (N : ℕ) (h_even : Even (N * (N + 1) / 2))
    (x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
    ((Finset.Icc 1 N).erase x).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem hx, Nat.card_Icc]
  have : 1 < N := by
    by_contra!
    have : N = 1 := by
      have := (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
      omega
    subst this
    exact absurd h_even (by decide)
  omega
