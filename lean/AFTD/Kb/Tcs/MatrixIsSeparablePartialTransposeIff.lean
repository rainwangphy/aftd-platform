import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable

/-!
# matrix_is_separable_partial_transpose_iff

Topic: quantum   Node: dc46eccb0975

Provenance: helper lemma. OP-2299; qutrit convolution, experiments 40125-40126 and 40163-40166.

Partial transpose on the second tensor factor preserves separability.
-/

theorem matrix_is_separable_partial_transpose_iff (dA dB : ℕ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    matrix_is_separable dA dB ρ ↔
      matrix_is_separable dA dB (Matrix.of fun p q => ρ (p.1,q.2) (q.1,p.2)) := by
  have forward (R : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
      (h : matrix_is_separable dA dB R) :
      matrix_is_separable dA dB (Matrix.of fun p q => R (p.1,q.2) (q.1,p.2)) := by
    rcases h with ⟨N, x, y, h⟩
    refine ⟨N, x, fun i j => star (y i j), ?_⟩
    intro p q
    simp only [Matrix.of_apply]
    rw [h (p.1,q.2) (q.1,p.2)]
    simp only [star_star]
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · exact forward ρ
  · intro h
    have hh := forward (Matrix.of fun p q => ρ (p.1,q.2) (q.1,p.2)) h
    have heq : (Matrix.of fun p q =>
        (Matrix.of fun r s => ρ (r.1,s.2) (s.1,r.2)) (p.1,q.2) (q.1,p.2)) = ρ := by
      ext p q
      simp only [Matrix.of_apply, Prod.mk.eta]
    rw [heq] at hh
    exact hh
