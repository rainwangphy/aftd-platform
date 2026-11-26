import AFTD.Prelude
import AFTD.Kb.Tcs.Op874IsMEdge
import AFTD.Kb.Tcs.Op874V

/-!
# op874M

Topic: graphs   Node: d78c350ad71c

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The perfect matching of the chain, as the unordered-pair image of the matching-edge relation.
-/

/-- The perfect matching of the chain, as a set of unordered pairs. -/
def op874M (k : ℕ) [NeZero k] : Set (Sym2 (op874V k)) := {e | ∃ u v, e = s(u, v) ∧ op874IsMEdge u v}
