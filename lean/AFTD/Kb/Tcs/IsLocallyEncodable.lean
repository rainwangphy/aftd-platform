import AFTD.Prelude

/-!
# is_locally_encodable

Topic: quantum   Node: 40a9b4ce4cc9

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec II.1

For a finite set of parties with finite dimension types d p, a state ψ in EuclideanSpace ℂ ((p : Parties) → d p) is locally encodable if there exists an orthonormal basis B of EuclideanSpace ℂ ((p : Parties) → d p) indexed by (p : Parties) → d p such that every basis element B j equals Matrix.toEuclideanLin V ψ for some unitary matrix V that decomposes as a tensor product of local unitaries u p.
-/

/-- A state in the multipartite Euclidean space is locally encodable if its local unitary orbit contains an orthonormal basis. -/
def is_locally_encodable {Parties : Type*} [Fintype Parties] [DecidableEq Parties] {d : Parties → Type*} [∀ p, Fintype (d p)] [∀ p, DecidableEq (d p)] (ψ : EuclideanSpace ℂ ((p : Parties) → d p)) : Prop := ∃ B : OrthonormalBasis ((p : Parties) → d p) ℂ (EuclideanSpace ℂ ((p : Parties) → d p)), ∀ j, ∃ V : Matrix.unitaryGroup ((p : Parties) → d p) ℂ, (∃ u : ∀ p, Matrix.unitaryGroup (d p) ℂ, V.1 = fun x y => ∏ p, (u p).1 (x p) (y p)) ∧ B j = Matrix.toEuclideanLin V.1 ψ
