import AFTD.Prelude

/-!
# fibonacci_word

Topic: combinatorics   Node: 9271c1ed81be

Provenance: formalization of a published result. Source: Algebraic Combinatorics on Words, Chapter 2

The sequence of binary Fibonacci words F_n over Bool, defined by F_0 = [false], F_1 = [false, true], and F_{n+2} = F_{n+1} ++ F_n.
-/

/-- The n-th finite Fibonacci word over {0, 1} (represented as false and true). -/
def fibonacci_word : ℕ → List Bool
| 0 => [false]
| 1 => [false, true]
| n + 2 => fibonacci_word (n + 1) ++ fibonacci_word n
