import AFTD.Prelude

/-!
# c

Topic: combinatorics   Node: 8d59608b476d

Provenance: formalization of a published result. Source: arXiv:2611.26732 Definition 1.1

For a group $G$ and an element $s \in G$, the local count $c_G(s)$ is the cardinality of the set of elements $g \in G$ such that $g \in \langle sg \rangle$ or $sg \in \langle g \rangle$.
-/

/-- The power-graph local count $c_G(s)$ of an element $s$ in a group $G$. -/
noncomputable def c (G : Type*) [Group G] (s : G) : ℕ := Nat.card {g : G | g ∈ Subgroup.zpowers (s * g) ∨ s * g ∈ Subgroup.zpowers g}
