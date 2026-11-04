import AFTD.Prelude

/-!
# norm_sub_smul_sq

Topic: combinatorics   Node: 307a356ab568

Provenance: helper lemma. arXiv:2611.00379, Lemma 3 proof

Let $V$ be a real inner product space, let $z \in V$, let $n \in V$ be a unit vector with $\|n\| = 1$, and let $a \in \mathbb{R}$. Then $\|z - a \cdot n\|^2 = \|z\|^2 - 2 a \langle n, z \rangle + a^2$.
-/

open scoped RealInnerProductSpace in
/-- Expansion of the squared norm of a difference with a scaled unit vector in a real inner product space. -/
lemma norm_sub_smul_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z n : V) (hn : ‖n‖ = 1) (a : ℝ) :
    ‖z - a • n‖ ^ 2 = ‖z‖ ^ 2 - 2 * a * ⟪n, z⟫ + a ^ 2 := by
  rw [norm_sub_sq_real]
  have h1 : ‖a • n‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, mul_pow, hn, one_pow, mul_one, Real.norm_eq_abs, sq_abs]
  rw [h1, real_inner_smul_right, real_inner_comm z n]
  ring
