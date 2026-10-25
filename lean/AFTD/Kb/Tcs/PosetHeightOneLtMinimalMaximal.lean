import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHeightOne

/-!
# poset_height_one_lt_minimal_maximal

Topic: combinatorics   Node: 18806b71a8cc

Provenance: helper lemma. step towards poset_height_one_reconstructible

If P has height one and x < y in P, then nothing lies below x and nothing lies above y. Consequently the elements below a comparable pair form an antichain, and every comparable pair joins a minimal element to a maximal one: the poset is bipartite between its minimal and maximal elements.
-/

/-- In a height-one ordered set, the lower element of a comparable pair is minimal and the upper element is maximal. -/
theorem poset_height_one_lt_minimal_maximal (P : Type) [PartialOrder P] (hP : poset_height_one P) {x y : P} (hxy : x < y) : (∀ z : P, ¬ (z < x)) ∧ (∀ z : P, ¬ (y < z)) := by
  obtain ⟨-, hchain⟩ := hP
  exact ⟨fun z hz => hchain z x y ⟨hz, hxy⟩, fun z hz => hchain x y z ⟨hxy, hz⟩⟩
