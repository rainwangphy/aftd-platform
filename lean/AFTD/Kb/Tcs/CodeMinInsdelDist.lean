import AFTD.Prelude
import AFTD.Kb.Tcs.InsdelDist

/-!
# code_min_insdel_dist

Topic: information   Node: 40e173cb8e7f

Provenance: formalization of a published result. Source: arXiv:2611.21275 Section II-B

For any field $F$ and any $F$-submodule $C$ of $\mathrm{Fin}\,n \to F$, the minimum insertion-deletion distance of $C$ is the infimum in $\mathbb{N}$ of the set of distances $d$ for which there exist distinct codewords $u, v \in C$ such that $\mathrm{insdel\_dist}\,u\,v = d$.
-/

/-- The minimum insertion-deletion distance of a linear code over a field F. -/
noncomputable def code_min_insdel_dist {n : ℕ} {F : Type*} [Field F]
    (C : Submodule F (Fin n → F)) : ℕ := sInf {d : ℕ | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ insdel_dist u v = d}
