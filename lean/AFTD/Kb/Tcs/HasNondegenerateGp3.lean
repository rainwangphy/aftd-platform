import AFTD.Prelude

/-!
# has_nondegenerate_gp3

Topic: combinatorics   Node: b96ee6404a50

Provenance: formalization of a published result. Source: arXiv:2610.34758, Definition 1.1

A set $D$ in a commutative ring contains a nondegenerate three-term geometric progression if there exist $x, r$ with $x \neq 0$, $r \neq 0$, and $r^2 \neq 1$ such that $x, x r, x r^2 \in D$.
-/

/-- A set in a commutative ring contains a nondegenerate three-term geometric progression if there exist non-zero x, r with r^2 ≠ 1 such that x, xr, xr^2 ∈ D. -/
def has_nondegenerate_gp3 {F : Type*} [CommRing F] (D : Set F) : Prop := ∃ x r : F, x ≠ 0 ∧ r ≠ 0 ∧ r ^ 2 ≠ 1 ∧ x ∈ D ∧ x * r ∈ D ∧ x * r ^ 2 ∈ D
