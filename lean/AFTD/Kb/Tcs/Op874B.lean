import AFTD.Prelude
import AFTD.Kb.Tcs.Op874V

/-!
# op874B

Topic: graphs   Node: e0fd25a216b0

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The bit-1 (B) vertex at position j of block i.
-/

/-- The bit-1 (B) vertex at position j of block i. -/
def op874B {k : ℕ} (i : Fin k) (j : Fin 8) : op874V k := ((i, true), j)
