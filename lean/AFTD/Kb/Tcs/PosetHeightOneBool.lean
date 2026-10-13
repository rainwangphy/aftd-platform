import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHeightOne

/-!
# poset_height_one_bool

Topic: combinatorics   Node: bd8e12cb4f87

Provenance: helper lemma. Sanity lemma for poset_height_one (arXiv:2610.12690).

The two-element chain false < true has height one.
-/

theorem poset_height_one_bool : poset_height_one Bool := by
  refine ⟨⟨false, true, by decide⟩, ?_⟩
  decide
