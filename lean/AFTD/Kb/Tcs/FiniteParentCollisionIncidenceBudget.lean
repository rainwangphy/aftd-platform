import AFTD.Prelude
import AFTD.Kb.Tcs.OrientedOverlapMultiplicityBudget

/-!
# finite_parent_collision_incidence_budget

Topic: combinatorics   Node: 191a8bec90a2

Provenance: helper lemma. Finite collision-charge assembly for the OP-110 small-overlap route.

For finite repeated-pair parent sets and charge sets contained in them, if a two-parent pair receives at most one charge, the number of parents in their union plus the total number of charges is at most three times their total excess multiplicity.
-/

theorem finite_parent_collision_incidence_budget
    (ι α : Type) [DecidableEq ι] [DecidableEq α]
    (S : Finset ι) (P C : ι → Finset α)
    (hm : ∀ e ∈ S, 2 ≤ (P e).card)
    (hc : ∀ e ∈ S, C e ⊆ P e)
    (h2 : ∀ e ∈ S, (P e).card = 2 → (C e).card ≤ 1) :
    (S.biUnion P).card + (∑ e ∈ S, (C e).card) ≤
      3 * ∑ e ∈ S, ((P e).card - 1) := by
  have hc' : ∀ e ∈ S, (C e).card ≤ (P e).card := by
    intro e he
    exact Finset.card_le_card (hc e he)
  have hb := oriented_overlap_multiplicity_budget ι S (fun e => (P e).card)
    (fun e => (C e).card) hm hc' h2
  have hd : (S.biUnion P).card ≤ ∑ e ∈ S, (P e).card := Finset.card_biUnion_le
  omega
