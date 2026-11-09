import AFTD.Prelude

/-!
# polynomial_subspace

Topic: information   Node: 0f950474856e

Provenance: formalization of a published result. Source: arXiv:2611.04947 Section 1 and Section 3

For an element x in an extension field L over F and an integer k, the polynomial subspace $U_k(x)$ is the F-span of the powers $1, x, \dots, x^{k-1}$.
-/

/-- The polynomial subspace U_k(x) = Span_F(1, x, ..., x^{k-1}). -/
def polynomial_subspace (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]
    (k : ℕ) (x : L) : Submodule F L := Submodule.span F (Set.range (fun (i : Fin k) => x ^ (i : ℕ)))
