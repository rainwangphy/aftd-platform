import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# is_picking_sequence_pne

Topic: fair_division   Node: 5e90af072fdc

Provenance: formalization of a published result. Source: arXiv:2610.23686 (Revisiting the Fairness of Pure Nash Equilibria of Round-Robin), Definition 3; arXiv:2610.23040 Definition 2.3

A profile of reported strict rankings is a pure Nash equilibrium of the picking-sequence mechanism if no agent can obtain a bundle of strictly higher true value by unilaterally changing its reported ranking.
-/

/-- A report profile is a pure Nash equilibrium of the picking-sequence mechanism if no agent can obtain a bundle of strictly higher true value `v` by unilaterally changing its reported strict ranking. -/
def is_picking_sequence_pne {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (v : SocialChoice.FairDivision.Indivisible.Valuation N G) (seq : List N)
    (rank : N → Fin m ≃ G) : Prop :=
  ∀ (i : N) (r : Fin m ≃ G),
    v.val i (picking_sequence_outcome seq (Function.update rank i r) i) ≤
      v.val i (picking_sequence_outcome seq rank i)
