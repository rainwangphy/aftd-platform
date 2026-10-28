import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad

/-!
# distance_set

Topic: combinatorics   Node: dd5aaa155a32

Provenance: formalization of a published result. Source: arXiv:2610.34758 Section 1, Eq (1.1)

The distance set $\Delta(E)$ of a subset $E \subset (\mathbb{Z}/p\mathbb{Z})^d$ is the set of values $Q_d(x - y)$ for all $x, y \in E$.
-/

/-- The distance set of a subset of (ZMod p)^d under the standard quadratic form. -/
def distance_set (d : ℕ) {p : ℕ} (E : Set (Fin d → ZMod p)) : Set (ZMod p) := { standard_quad d (x - y) | (x ∈ E) (y ∈ E) }
