import AFTD.Prelude

/-!
# group_is_complete_mapping

Topic: combinatorics   Node: 2740f81335d4

Provenance: formalization of a published result. Source: arXiv:2610.17631 (Complete mappings stabilizing Sylow 2-subgroups in central quotients of special linear groups), Sec. 1 (definition of a complete mapping).

A complete mapping of a group G is a permutation θ of G such that x ↦ xθ(x) is also a permutation of G.
-/

/-- A complete mapping: `θ` and `x ↦ x * θ x` are both bijections of `G`. -/
def group_is_complete_mapping {G : Type*} [Group G] (θ : G → G) : Prop :=
  Function.Bijective θ ∧ Function.Bijective fun x => x * θ x
