import AFTD.Prelude

/-!
# symmetric_counterexample_func

Topic: combinatorics   Node: 04925be59479

Provenance: formalization of a published result. Source: arXiv:2611.06744, Theorem 1

For any integer n, the symmetric Boolean function F_n on (Fin n → ZMod 2) is the sum over j from 0 to n / 4 of the elementary symmetric Boolean polynomial of degree 2j, where σ_{2j}(x) is the sum over subsets s of Fin n of size 2j of the product of coordinates in s.
-/

/-- The symmetric Boolean function F_n = ∑_{j=0}^{n/4} σ_{2j} on (Fin n → ZMod 2). -/
def symmetric_counterexample_func (n : ℕ) (x : Fin n → ZMod 2) : ZMod 2 := ∑ j ∈ Finset.range (n / 4 + 1), ∑ s ∈ Finset.powersetCard (2 * j) Finset.univ, ∏ i ∈ s, x i
