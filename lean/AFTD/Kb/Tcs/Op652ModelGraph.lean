import AFTD.Prelude
import AFTD.Kb.Tcs.Op652Rel
import AFTD.Kb.Tcs.Op652RelDecidable
import AFTD.Kb.Tcs.Op652ProgressionImage
import AFTD.Kb.Tcs.Op652DivisorList

/-!
# op652_model_graph

Topic: graphs   Node: 37f0b1290689

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The 72-vertex model graph: the same `fromRel` construction as `coprime_divisor_progression_graph 1248191226 37 1`, but on the explicit small carriers `op652_divisor_list` and `op652_progression_image` rather than the kernel-unfriendly `Nat.divisors 1248191226`.
-/

/-- The model graph on the explicit 36+36 carriers; `abbrev` so the automatic `fromRel` decidability instance (via `op652_rel_decidable`) is found, letting `decide` evaluate its degrees and cut counts. -/
abbrev op652_model_graph : SimpleGraph (↥op652_divisor_list ⊕ ↥op652_progression_image) := SimpleGraph.fromRel op652_rel
