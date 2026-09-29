import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner

/-!
# condorcet_winner_unique

Topic: social_choice   Node: f4e7fbf7e179

If x and y are both Condorcet winners under a preference profile P with a finite voter set V, then x = y.
-/

/-- A Condorcet winner is unique: no two distinct alternatives can both be Condorcet winners. -/
theorem condorcet_winner_unique {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x y : A)
    (hx : condorcet_winner P x) (hy : condorcet_winner P y) :
    x = y := by
  by_contra hne
  have h1 := hx y (Ne.symm hne)
  have h2 := hy x hne
  omega
