import AFTD.Prelude

/-!
# SubsetSumToPartition.SubsetSum

Topic: np_completeness   Node: 7b5a68f145ad

Provenance: formalization of a published result. Source: TCSlib, `SubsetSumToPartition.SubsetSum`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean (Apache-2.0); 1 verbatim; compiled here.

Given a weight function $w : U \to \mathbb{N}$ on a finite type $U$ and a target
$T \in \mathbb{N}$, the predicate asserts that some subset $S \subseteq U$ has total weight
exactly $T$, i.e.\ $\exists S,\ \sum_{a \in S} w(a) = T$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {U : Type*} [Fintype U] [DecidableEq U] in
/-- The Subset Sum problem: Given a weight function `w` and a target `T`, does there exist a subset `S` of `U` whose weights sum exactly to `T`? -/
noncomputable def SubsetSumToPartition.SubsetSum (w : U → ℕ) (T : ℕ) : Prop :=
  ∃ S : Finset U, (∑ a ∈ S, w a) = T
