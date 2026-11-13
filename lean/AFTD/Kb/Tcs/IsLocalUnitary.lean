import AFTD.Prelude

/-!
# is_local_unitary

Topic: quantum   Node: dfe4a7609865

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec II.1

For a finite set of parties each with a finite dimension type d p, a unitary matrix U on the product index type (p : Parties) → d p over ℂ is a local unitary if there exists a family of unitary matrices u p in Matrix.unitaryGroup (d p) ℂ such that the matrix entry U x y equals the product over all p of (u p) (x p) (y p).
-/

/-- A unitary matrix on the product basis of a multipartite system is local if it is the Kronecker/tensor product of unitary matrices on the subsystems. -/
def is_local_unitary {Parties : Type*} [Fintype Parties] [DecidableEq Parties] {d : Parties → Type*} [∀ p, Fintype (d p)] [∀ p, DecidableEq (d p)] (U : Matrix.unitaryGroup ((p : Parties) → d p) ℂ) : Prop := ∃ u : ∀ p, Matrix.unitaryGroup (d p) ℂ, U.1 = fun x y => ∏ p, (u p).1 (x p) (y p)
