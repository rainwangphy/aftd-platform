import AFTD.Prelude

/-!
# op874V

Topic: graphs   Node: 9c30860217a7

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The vertex set of the gadget chain: (block index, bit, local position).
-/

/-- Vertex type of the op874 mixed gadget chain. -/
def op874V (k : ℕ) : Type := (Fin k × Bool) × Fin 8
