import AFTD.Prelude
import AFTD.Kb.Tcs.IsReducedLatinSquare
import AFTD.Kb.Tcs.LatinSquareIsAdd
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# is_reduced_latin_square_add

Topic: combinatorics   Node: d2f1d72c4e0a

Provenance: formalization of a published result. Source: folklore

For every non-zero natural number $n$, the addition table on $\text{Fin } n$ is a reduced Latin square of order $n$.
-/

/-- The addition table on Fin n is a reduced Latin square. -/
theorem is_reduced_latin_square_add (n : ℕ) [NeZero n] :
    is_reduced_latin_square (fun i j : Fin n => i + j) := ⟨latin_square_is_add n, zero_add, add_zero⟩
