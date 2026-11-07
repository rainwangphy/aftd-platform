import AFTD.Prelude
import AFTD.Kb.Tcs.HasOrderedCopy
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# has_ordered_copy_self

Topic: graphs   Node: acf28bde2703

Provenance: helper lemma. arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

Every ordered graph contains an ordered copy of itself via the identity map.
-/

/-- Every ordered graph contains an ordered copy of itself. -/
theorem has_ordered_copy_self {α : Type*} [LinearOrder α] (G : SimpleGraph α) :
    has_ordered_copy G G := ⟨id, strictMono_id, fun _ _ h => h⟩
