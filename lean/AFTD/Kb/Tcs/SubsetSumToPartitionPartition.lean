import AFTD.Prelude

/-!
# SubsetSumToPartition.Partition

Topic: np_completeness   Node: 18950c8175e0

Provenance: formalization of a published result. Source: TCSlib, `SubsetSumToPartition.Partition`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean (Apache-2.0); 1 verbatim; compiled here.

Given a weight function $v : U \to \mathbb{N}$ on a finite type $U$, the predicate asserts
that some subset $S \subseteq U$ has the same total weight as its complement, i.e.\
$\exists S,\ \sum_{b \in S} v(b) = \sum_{b \in S^{c}} v(b)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {U : Type*} [Fintype U] [DecidableEq U] in
/-- The Partition problem: Given a finite set `U` and a weight function `v`, does there exist a subset `S` whose sum equals the sum of its complement `Sᶜ`? -/
noncomputable def SubsetSumToPartition.Partition (v : U → ℕ) : Prop :=
  ∃ S : Finset U, (∑ b ∈ S, v b) = (∑ b ∈ Sᶜ, v b)
