import AFTD.Prelude
import AFTD.Kb.Tcs.C

/-!
# M

Topic: combinatorics   Node: 542ed53c0ac9

Provenance: formalization of a published result. Source: arXiv:2611.26732 Proposition 1.6

For a group $G$, $M$ is the set of elements $s \in G \setminus \{1\}$ such that $c_G(x) \le c_G(s)$ for all $x \in G \setminus \{1\}$.
-/

/-- The set $M$ of non-identity elements of $G$ achieving the maximum power-graph local count $c_G(s)$. -/
noncomputable def M (G : Type*) [Group G] : Set G := {s : G | s ≠ 1 ∧ ∀ x ≠ 1, c G x ≤ c G s}
