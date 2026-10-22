import AFTD.Prelude

/-!
# circulant_mul_left_comm

Topic: combinatorics   Node: b15e10c6e7d8

Provenance: helper lemma. helper for the Goethals-Seidel array identity, arXiv:2610.27175 Theorem 3

Circulant matrices over Fin m commute past one another: circulant v (circulant w Z) = circulant w (circulant v Z).
-/

theorem circulant_mul_left_comm {m : ℕ} [NeZero m] (v w : Fin m → ℤ)
    (Z : Matrix (Fin m) (Fin m) ℤ) :
    Matrix.circulant v * (Matrix.circulant w * Z)
      = Matrix.circulant w * (Matrix.circulant v * Z) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.circulant_mul_comm]
