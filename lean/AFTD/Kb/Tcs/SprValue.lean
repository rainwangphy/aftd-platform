import AFTD.Prelude
import AFTD.Kb.Tcs.SprSignCount
import AFTD.Kb.Tcs.SprMove

/-!
# spr_value

Topic: learning   Node: 88f42a35538a

Provenance: formalization of a published result. Source: arXiv:2610.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2 (the game is one of perfect information, so the value with randomized strategies equals this pure minimax value)

The minimax value of the sign-preservation-with-reuse game with r rounds left from a given board: the pointer (maximizer) may stop or select an empty cell j; the labeler (minimizer) then removes any subset of the minus signs to the left of j and the plus signs to the right of j and places a plus or minus in j; the game ends when the pointer stops, the rounds run out, or no cell is empty, and the payoff is the number of signs on the board.
-/

/-- Value of the sign-preservation-with-reuse game with `r` rounds left from board `b`, under optimal play: the pointer (maximizer) may stop, or select an empty cell `j`; the labeler (minimizer) then empties any legal set `R` (minus signs left of `j`, plus signs right of `j`) and places a sign in `j`. The game ends when the pointer stops, no rounds are left, or no cell is empty; the payoff is the number of signs on the board. -/
def spr_value (n : ℕ) : ℕ → (Fin n → Option Bool) → ℕ := fun
  | 0, b => spr_sign_count b
  | r + 1, b =>
    max (spr_sign_count b)
      ((Finset.univ.filter fun j => b j = none).sup fun j =>
        ((Finset.univ : Finset (Finset (Fin n) × Bool)).filter
            fun p => ∀ i ∈ p.1, (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true)).inf'
          ⟨(∅, true), Finset.mem_filter.2
            ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩⟩
          fun p => spr_value n r (spr_move b j p.1 p.2))
