import AFTD.Prelude
import AFTD.Kb.Tcs.Op874IsEdge
import AFTD.Kb.Tcs.Op874V

/-!
# op874E

Topic: graphs   Node: f6195c85e93c

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The edge set of the chain, as the unordered-pair image of the edge relation.
-/

/-- The edge set of the chain, as a set of unordered pairs. -/
def op874E (k : ℕ) [NeZero k] : Set (Sym2 (op874V k)) := {e | ∃ u v, e = s(u, v) ∧ op874IsEdge u v}
