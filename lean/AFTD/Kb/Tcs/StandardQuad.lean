import AFTD.Prelude

/-!
# standard_quad

Topic: combinatorics   Node: cf9463c95680

Provenance: formalization of a published result. Source: arXiv:2610.34758 Section 1, Eq (1.1)

The standard quadratic form $Q_d$ on $(\mathbb{Z}/p\mathbb{Z})^d$, defined by $Q_d(x) = \sum_{i} x_i^2$.
-/

/-- The standard quadratic form Q_d on (ZMod p)^d. -/
def standard_quad (d : ℕ) {p : ℕ} (x : Fin d → ZMod p) : ZMod p := ∑ i, (x i) ^ 2
