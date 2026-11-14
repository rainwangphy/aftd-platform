import AFTD.Prelude

/-!
# is_bipartite_locally_encodable

Topic: quantum   Node: 01f7ed479c6f

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.1

A bipartite quantum state ψ in EuclideanSpace ℂ (m × n) is locally encodable if there exists an orthonormal basis B of EuclideanSpace ℂ (m × n) indexed by m × n such that each basis element B j equals Matrix.toEuclideanLin (Matrix.kronecker uA.1 uB.1) ψ for some unitary matrices uA in Matrix.unitaryGroup m ℂ and uB in Matrix.unitaryGroup n ℂ.
-/

/-- A bipartite quantum state ψ in EuclideanSpace ℂ (m × n) is locally encodable if its local unitary orbit contains an orthonormal basis of EuclideanSpace ℂ (m × n). -/
def is_bipartite_locally_encodable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ψ : EuclideanSpace ℂ (m × n)) : Prop := ∃ B : OrthonormalBasis (m × n) ℂ (EuclideanSpace ℂ (m × n)),
    ∀ j, ∃ (uA : Matrix.unitaryGroup m ℂ) (uB : Matrix.unitaryGroup n ℂ),
      B j = Matrix.toEuclideanLin (Matrix.kronecker uA.1 uB.1) ψ
