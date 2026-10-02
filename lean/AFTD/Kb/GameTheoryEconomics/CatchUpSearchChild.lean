import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_search_child

Topic: combinatorial_games   Node: 22cb223f87d7

One move of the search: if two pairs of Booleans decide 'win' and 'not loss' for outcomes E1 and E2, then choosing between the negated searches of E1 (when the turn passes) and the searches of E2 decides 'win' and 'not loss' for the corresponding outcome, E1 negated or E2.
-/

/-- One child of a search node agrees with the outcome, through `neg` when the turn passes. -/
theorem catch_up_search_child (P : Prop) [Decidable P] (E1 E2 : CatchUpOutcome)
    (s1t s1f s2t s2f : Bool)
    (h1 : (s1t = true ↔ E1 = .win) ∧ (s1f = true ↔ E1 ≠ .loss))
    (h2 : (s2t = true ↔ E2 = .win) ∧ (s2f = true ↔ E2 ≠ .loss)) :
    ((if P then !s1f else s2t) = true ↔ (if P then E1.neg else E2) = .win) ∧
    ((if P then !s1t else s2f) = true ↔ (if P then E1.neg else E2) ≠ .loss) := by
  split_ifs
  · constructor
    · rw [Bool.not_eq_true', ← Bool.not_eq_true, h1.2]; cases E1 <;> simp [CatchUpOutcome.neg]
    · rw [Bool.not_eq_true', ← Bool.not_eq_true, h1.1]; cases E1 <;> simp [CatchUpOutcome.neg]
  · exact h2
