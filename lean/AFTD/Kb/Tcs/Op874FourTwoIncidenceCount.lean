import AFTD.Prelude

/-!
# op874_four_two_incidence_count

Topic: graphs   Node: 970f04ab516f

Provenance: helper lemma. Incidence and matching reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

In a four-by-two incidence system, the total number of incidences of any finite set of right vertices is twice its cardinality.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem op874_four_two_incidence_count
    {L E : Type*} [Fintype L] [Fintype E] [DecidableEq L] [DecidableEq E]
    (inc : L → E → Prop) [DecidableRel inc]
    (hright : ∀ e, (univ.filter fun l => inc l e).card = 2)
    (X : Finset E) :
    (∑ l : L, (X.filter fun e => inc l e).card) = 2 * X.card := by
  have h := @Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow L E inc univ X _
  simpa [Finset.bipartiteAbove, Finset.bipartiteBelow, hright, mul_comm] using h
