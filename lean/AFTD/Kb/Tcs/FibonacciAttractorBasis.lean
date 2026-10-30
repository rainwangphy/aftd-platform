import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciSingularWord
import AFTD.Kb.Tcs.FibonacciBoundaryWord

/-!
# fibonacci_attractor_basis

Topic: combinatorics   Node: 37dc581df1fe

Provenance: formalization of a published result. Source: arXiv:2610.10950 Smallest String Attractors and Minimal Coverage Certificates of Thue--Morse Words

For a natural number n, fibonacci_attractor_basis n is the finite set (Finset (List Bool)) formed by the union of: (1) the image under fibonacci_singular_word of Finset.range (n - 1) (natural numbers j < n - 1), and (2) the image under fibonacci_boundary_word of the filter of Finset.Icc 3 (n - 4) on j % 2 = n % 2.
-/

/-- The canonical attractor basis B_n consisting of singular words S_j for 0 <= j <= n-2 and boundary words E_j for 3 <= j <= n-4 with j = n mod 2. -/
def fibonacci_attractor_basis (n : ℕ) : Finset (List Bool) := ((Finset.range (n - 1)).image fibonacci_singular_word) ∪
  (((Finset.Icc 3 (n - 4)).filter (fun j => j % 2 = n % 2)).image fibonacci_boundary_word)
