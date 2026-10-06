import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner

/-!
# condorcet_winner_of_subsingleton

Topic: social_choice   Node: bcb6be0afeff

Provenance: original. Related work: machine-posed degenerate case of the Condorcet-winner definition (at most one alternative); trivial, no novelty claimed

When the set of alternatives is a subsingleton, any alternative is a Condorcet winner under any preference profile.
-/

/-- In a single-alternative setting, the unique alternative is vacuously a Condorcet winner. -/
theorem condorcet_winner_of_subsingleton {V A : Type*} [Fintype V]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)] [Subsingleton A] (x : A) :
    condorcet_winner P x := by
  intro y hy
  exfalso
  exact hy (Subsingleton.elim y x)
