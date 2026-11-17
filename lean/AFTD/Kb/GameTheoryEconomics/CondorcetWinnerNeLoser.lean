import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner
import AFTD.Kb.GameTheoryEconomics.CondorcetLoser

/-!
# condorcet_winner_ne_loser

Topic: social_choice   Node: 038c6cfacfe9

Provenance: formalization of a published result. Source: Fishburn 1977

Under a preference profile P with a finite voter set V, if an alternative x is a Condorcet winner and y is a Condorcet loser, and there exists at least one alternative distinct from x, then x ≠ y.
-/

/-- In any election with at least two alternatives, a Condorcet winner cannot be a Condorcet loser. -/
theorem condorcet_winner_ne_loser {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x y : A)
    (hw : condorcet_winner P x) (hl : condorcet_loser P y)
    (z : A) (hz : z ≠ x) : x ≠ y := by
  rintro rfl
  have h1 := hw z hz
  have h2 := hl z hz
  omega
