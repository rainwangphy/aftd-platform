import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad

/-!
# standard_quad_cons_cons

Topic: combinatorics   Node: e6b45576c586

Provenance: helper lemma. step towards cylinder_construction_distance_set

For any natural number $d$, prime $p$, scalars $a, b \in \mathbb{Z}/p\mathbb{Z}$, and vector $v \in (\mathbb{Z}/p\mathbb{Z})^d$, $Q_{d+2}((a, b, v)) = a^2 + b^2 + Q_d(v)$.
-/

/-- The standard quadratic form Q_{d+2} evaluated on a vector with two prepended coordinates equals a^2 + b^2 + Q_d(v). -/
theorem standard_quad_cons_cons (d : ℕ) {p : ℕ} (a b : ZMod p) (v : Fin d → ZMod p) :
    standard_quad (d + 2) (Matrix.vecCons a (Matrix.vecCons b v)) = a ^ 2 + b ^ 2 + standard_quad d v := by
  simp [standard_quad, Matrix.vecCons, Fin.sum_univ_succ, add_assoc]
