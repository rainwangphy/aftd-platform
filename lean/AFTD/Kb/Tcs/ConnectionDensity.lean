import AFTD.Prelude
import AFTD.Kb.Tcs.C

/-!
# connection_density

Topic: combinatorics   Node: 25bfe7ae0ad3

Provenance: formalization of a published result. Source: arXiv:2611.26732 Definition 1.1

Given a type $G$ with `[Group G]` and `[Fintype G]`, and a finite set $S : \mathrm{Finset}\ G$, `connection_density G S` is the rational number in $\mathbb{Q}$ defined by $(\sum_{s \in S} (c\ G\ s : \mathbb{Q})) / ((\mathrm{Fintype.card}\ G : \mathbb{Q}) \cdot (S.\mathrm{card} : \mathbb{Q}))$, evaluating to $0$ when $S$ is empty.
-/

/-- The edge intersection density of a connection set $S$ in a finite group $G$. -/
noncomputable def connection_density (G : Type*) [Group G] [Fintype G] (S : Finset G) : ℚ := (∑ s ∈ S, (c G s : ℚ)) / ((Fintype.card G : ℚ) * (S.card : ℚ))
