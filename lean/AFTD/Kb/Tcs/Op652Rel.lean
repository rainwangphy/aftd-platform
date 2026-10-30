import AFTD.Prelude
import AFTD.Kb.Tcs.Op652DivisorList
import AFTD.Kb.Tcs.Op652ProgressionImage

/-!
# op652_rel

Topic: graphs   Node: dd6fdae7a850

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The adjacency relation of the coprime divisor-progression graph on the small carriers: a divisor d and a progression term x are related iff d and x are coprime in ℤ; no edges within a side.
-/

/-- The cross-side coprimality relation on the model carriers, identical to the one defining `coprime_divisor_progression_graph`. -/
def op652_rel (u v : ↥op652_divisor_list ⊕ ↥op652_progression_image) : Prop := match u, v with
    | Sum.inl d, Sum.inr x => IsCoprime (d.1 : ℤ) x.1
    | _, _ => False
