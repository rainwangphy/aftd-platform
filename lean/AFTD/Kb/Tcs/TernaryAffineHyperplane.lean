import AFTD.Prelude

/-!
# ternary_affine_hyperplane

Topic: combinatorics   Node: 851e6312d9dd

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

Given an explicit natural number n, a vector a : Fin n → ZMod 3, and a scalar b : ZMod 3, the ternary affine hyperplane is the finite set (Finset) of all vectors x : Fin n → ZMod 3 such that the sum over all i : Fin n of a i * x i equals b.
-/

/-- The affine hyperplane in (Fin n → ZMod 3) with equation sum_i a_i * x_i = b as a Finset. -/
def ternary_affine_hyperplane (n : ℕ) (a : Fin n → ZMod 3) (b : ZMod 3) : Finset (Fin n → ZMod 3) := Finset.filter (fun x => (∑ i : Fin n, a i * x i) = b) Finset.univ
