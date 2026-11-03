import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteParentCollisionIncidenceBudget

/-!
# finite_parent_collision_budget_with_cover

Topic: combinatorics   Node: 37b3c0bc45c3

Provenance: helper lemma. Finite collision-charge assembly for the OP-110 small-overlap route.

Under the same repeated-pair parent and charge assumptions, any dirty set covered by the parent sets and any missing set no larger than the total charges have combined size at most three times the excess multiplicity.
-/

theorem finite_parent_collision_budget_with_cover
    (ι α β : Type) [DecidableEq ι] [DecidableEq α] [DecidableEq β]
    (S : Finset ι) (P C : ι → Finset α) (dirty : Finset α) (missing : Finset β)
    (hcover : dirty ⊆ S.biUnion P)
    (hcharge : missing.card ≤ ∑ e ∈ S, (C e).card)
    (hm : ∀ e ∈ S, 2 ≤ (P e).card)
    (hc : ∀ e ∈ S, C e ⊆ P e)
    (h2 : ∀ e ∈ S, (P e).card = 2 → (C e).card ≤ 1) :
    dirty.card + missing.card ≤ 3 * ∑ e ∈ S, ((P e).card - 1) := by
  have hdirty := Finset.card_le_card hcover
  have hbudget := finite_parent_collision_incidence_budget ι α S P C hm hc h2
  omega
