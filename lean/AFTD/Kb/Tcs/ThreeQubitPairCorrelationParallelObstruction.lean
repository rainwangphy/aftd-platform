import AFTD.Prelude

/-!
# three_qubit_pair_correlation_parallel_obstruction

Topic: quantum   Node: 549575aef974

Provenance: helper lemma.

For the displayed integer correlation matrices of a particular three-qubit state, no real unit vectors a and b can simultaneously satisfy the AB pair-orthogonality equation and make the AC and BC correlation vectors parallel. The algebraic assertion is stated explicitly and does not itself certify the matrices came from that state.
-/

theorem three_qubit_pair_correlation_parallel_obstruction
    (x y z u v w t : ℝ)
    (ha : x^2 + y^2 + z^2 = 1)
    (hb : u^2 + v^2 + w^2 = 1)
    (e1 : 2*u = t*(2*x + 4*z))
    (e2 : -4*u + 6*v + 2*w = t*(-8*x + 2*y + 2*z))
    (e3 : -4*u + 4*v + 2*w = t*(-4*x + 6*y))
    (epair : x*(6*u - 8*v) + y*(-4*u + 2*v + 6*w) + z*(4*u + 4*v + 2*w) = 0) :
    False := by
  have hu : u = t*(x + 2*z) := by nlinarith [e1]
  have hv : v = t*(-2*x - 2*y + z) := by nlinarith [e1, e2, e3]
  have hw : w = t*(4*x + 7*y + 2*z) := by nlinarith [e1, e2, e3]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [zero_mul] at hu hv hw
    rw [hu, hv, hw] at hb
    norm_num at hb
  let Q := 22*x^2 + 32*x*y + 8*x*z + 38*y^2 + 12*y*z + 16*z^2
  have hq : 0 < Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (x+y), sq_nonneg (x+z), sq_nonneg (y+z),
      sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have heq : t * Q = 0 := by
    rw [hu, hv, hw] at epair
    dsimp [Q]
    nlinarith [epair]
  exact (mul_ne_zero ht (ne_of_gt hq)) heq
