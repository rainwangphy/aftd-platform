import AFTD.Prelude
import AFTD.Kb.Tcs.Op874V

/-!
# op874A

Topic: graphs   Node: f8831e119486

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The bit-0 (A) vertex at position j of block i.
-/

/-- The bit-0 (A) vertex at position j of block i. -/
def op874A {k : ℕ} (i : Fin k) (j : Fin 8) : op874V k := ((i, false), j)
