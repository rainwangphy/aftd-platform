import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciWord

/-!
# fibonacci_singular_word

Topic: combinatorics   Node: 061988673353

Provenance: formalization of a published result. Source: European Journal of Combinatorics 15(6):587-598 (1994)

The j-th singular word S_j, defined for j ≥ 0 by prefixing the last symbol of F_{j-1} (which is true if j is even and false if j is odd) to F_j with its final symbol deleted.
-/

/-- The j-th singular word S_j: last(F_{j-1}) followed by F_j with its last symbol dropped. -/
def fibonacci_singular_word (j : ℕ) : List Bool := decide (Even j) :: (fibonacci_word j).dropLast
