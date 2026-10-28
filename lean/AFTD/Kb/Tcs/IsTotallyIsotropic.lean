import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad

/-!
# is_totally_isotropic

Topic: combinatorics   Node: c84394829be0

Provenance: formalization of a published result. Source: arXiv:2610.34758 Section 2.1

A subspace $W \subset (\mathbb{Z}/p\mathbb{Z})^d$ is totally isotropic with respect to the standard quadratic form $Q_d$ if $Q_d(w) = 0$ for all $w \in W$.
-/

/-- A subspace is totally isotropic if the standard quadratic form vanishes on it. -/
def is_totally_isotropic (d : ℕ) {p : ℕ} (W : Submodule (ZMod p) (Fin d → ZMod p)) : Prop := ∀ w ∈ W, standard_quad d w = 0
