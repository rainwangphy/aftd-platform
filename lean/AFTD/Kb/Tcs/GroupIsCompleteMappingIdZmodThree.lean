import AFTD.Prelude
import AFTD.Kb.Tcs.GroupIsCompleteMapping

/-!
# group_is_complete_mapping_id_zmod_three

Topic: combinatorics   Node: 0b2c0edfbdbf

Provenance: helper lemma. Sanity lemma for complete mappings, arXiv:2610.17631 (Complete mappings stabilizing Sylow 2-subgroups in central quotients of special linear groups), Sec. 1 (groups of odd order have the identity as a complete mapping).

In the cyclic group of order 3 the identity map is a complete mapping (x ↦ x² is a bijection in odd order).
-/

theorem group_is_complete_mapping_id_zmod_three :
    group_is_complete_mapping (fun x : Multiplicative (ZMod 3) => x) := by
  refine ⟨Function.bijective_id, ?_⟩
  decide
