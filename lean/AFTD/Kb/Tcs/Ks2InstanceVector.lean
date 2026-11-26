import AFTD.Prelude

/-!
# ks2_instance_vector

Topic: np_completeness   Node: e253f53da5be

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1 (decision version KS_2(c) of the algorithmic Kadison-Singer problem): an input vector. Encoding choice (the paper fixes none): an input vector is given by a pair (t, w), t a rational and w a list of pairs of rationals, and stands for sqrt(t) times the vector with Gaussian-rational coordinates a_j + b_j i; this covers the paper's reduction, whose vectors are sqrt(alpha_r / q_v) times sign vectors.

With explicit arguments d : ℕ and p : ℚ × List (ℚ × ℚ), in this order, where p = (t, w): the complex vector Fin d → ℂ whose j-th coordinate is sqrt(t) * (a_j + b_j * i), where sqrt is the real square root Real.sqrt of t cast to ℝ (so it is 0 when t is negative), and (a_j, b_j) is the entry of the list w at position j (List.getD with default (0, 0), so (0, 0) when w has no entry at position j), the rationals a_j, b_j being cast to ℂ and i being Complex.I.
-/

/-- The vector of `ℂ^d` encoded by `(t, w)`: `sqrt t` times the Gaussian-rational vector `w`. -/
noncomputable def ks2_instance_vector (d : ℕ) (p : ℚ × List (ℚ × ℚ)) : Fin d → ℂ :=
  fun j => ((Real.sqrt (p.1 : ℝ) : ℝ) : ℂ) *
    ((((p.2.getD j.val (0, 0)).1 : ℚ) : ℂ) + (((p.2.getD j.val (0, 0)).2 : ℚ) : ℂ) * Complex.I)
