import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetLoser

/-!
# condorcet_loser_unique

Topic: social_choice   Node: 425d75181edc

Provenance: formalization of a published result. Source: Fishburn 1977

If x and y are both Condorcet losers under a preference profile P with a finite voter set V, then x = y.
-/

/-- A strict Condorcet loser, if one exists, is unique. -/
theorem condorcet_loser_unique {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] (x y : A)
    (hx : condorcet_loser P x) (hy : condorcet_loser P y) :
    x = y := by
  by_contra hne
  have h1 := hx y (Ne.symm hne)
  have h2 := hy x hne
  omega
