import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciWord

/-!
# fibonacci_boundary_word

Topic: combinatorics   Node: b502922ec4b9

Provenance: formalization of a published result. Source: arXiv:2610.10950 Smallest String Attractors and Minimal Coverage Certificates of Thue--Morse Words

The j-th boundary word E_j, defined for j ≥ 0 by prefixing the last symbol of F_{j-1} (which is true if j is even and false if j is odd) to F_j followed by false.
-/

/-- The j-th boundary word E_j: last(F_{j-1}) followed by F_j followed by 0 (false). -/
def fibonacci_boundary_word (j : ℕ) : List Bool := decide (Even j) :: fibonacci_word j ++ [false]
