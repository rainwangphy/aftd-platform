import AFTD.Prelude

/-!
# some_color_occurs_at_most_once_of_card_lt_twice

Topic: graphs   Node: f1a480df55ed

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

If a finite set has fewer than twice as many positions as colors, every coloring has some color occurring at most once.
-/

theorem some_color_occurs_at_most_once_of_card_lt_twice
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hsize : Fintype.card α < 2 * Fintype.card β) :
    ∃ k : β, ((Finset.univ : Finset α).filter fun i => f i = k).card ≤ 1 := by
  classical
  by_contra h
  have hge : ∀ k : β, 2 ≤ ((Finset.univ : Finset α).filter fun i => f i = k).card := by
    intro k
    have hk := not_exists.mp h k
    omega
  have hsum : (∑ _k : β, (2 : ℕ)) ≤
      ∑ k : β, ((Finset.univ : Finset α).filter fun i => f i = k).card := by
    exact Finset.sum_le_sum (fun k _ => hge k)
  have hfib : (∑ k : β, ((Finset.univ : Finset α).filter fun i => f i = k).card) =
      Fintype.card α := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset β) f
  have hbound : Fintype.card β * 2 ≤ Fintype.card α := by
    simpa [hfib] using hsum
  omega
