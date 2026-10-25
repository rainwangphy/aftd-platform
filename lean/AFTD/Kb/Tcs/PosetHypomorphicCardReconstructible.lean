import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHypomorphic

/-!
# poset_hypomorphic_card_reconstructible

Topic: combinatorics   Node: 69b506015d53

Provenance: helper lemma. step towards poset_height_one_reconstructible

Hypomorphic finite ordered sets have the same cardinality.
-/

/-- Finite ordered sets with the same deck have the same number of elements. -/
theorem poset_hypomorphic_card_reconstructible (P Q : Type) [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q] (h : poset_hypomorphic P Q) : Fintype.card P = Fintype.card Q := by
  obtain ⟨σ, -⟩ := h
  exact Fintype.card_congr σ
