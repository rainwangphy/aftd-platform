import AFTD.Prelude

/-!
# catch_up_sum_invariant

Topic: combinatorial_games   Node: 58ae28cfc108

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In any Catch-Up position, picking a piece x from remaining preserves the total sum of remaining pieces and both players' scores.
-/

/-- In any Catch-Up position, picking a piece x from remaining preserves the total sum of remaining pieces and both players' scores. -/
theorem catch_up_sum_invariant (remaining : Finset ℕ) (x : ℕ) (s_me s_opp : ℕ) (hx : x ∈ remaining) :
    (remaining.erase x).sum (fun y => y) + (s_me + x) + s_opp = remaining.sum (fun y => y) + s_me + s_opp := by
  have := Finset.sum_erase_add remaining (fun y => y) hx
  omega
