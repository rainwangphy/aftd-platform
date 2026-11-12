import AFTD.Prelude

/-!
# prioritized_borel_fork_majority_growth

Topic: automata   Node: 85658c85bd4f

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

If every history has a distinct stay extension and a distinct excursion extension colored by a bit, some common visible bit yields at least three halves as many histories.
-/

theorem prioritized_borel_fork_majority_growth {α : Type} [DecidableEq α]
    (S : Finset α) (stay exit : α → α)
    (hs : Function.Injective stay) (he : Function.Injective exit)
    (hdiff : ∀ a b, stay a ≠ exit b) (color : α → Bool) :
    ∃ bit, 3 * S.card ≤
      2 * ((S.image stay) ∪ ((S.filter fun a => color a = bit).image exit)).card := by
  classical
  have hdisj (bit : Bool) :
      Disjoint (S.image stay) ((S.filter fun a => color a = bit).image exit) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hy
    exact hdiff a b (hax.trans hbx.symm)
  have hcard (bit : Bool) :
      ((S.image stay) ∪ ((S.filter fun a => color a = bit).image exit)).card =
        S.card + (S.filter fun a => color a = bit).card := by
    rw [Finset.card_union_of_disjoint (hdisj bit),
      Finset.card_image_of_injective _ hs, Finset.card_image_of_injective _ he]
  have hp : (S.filter fun a => color a = true).card +
      (S.filter fun a => color a = false).card = S.card := by
    simpa using (Finset.card_filter_add_card_filter_not (s := S) (fun a => color a = true))
  by_cases h : (S.filter fun a => color a = true).card ≤
      (S.filter fun a => color a = false).card
  · refine ⟨false, ?_⟩
    rw [hcard]
    omega
  · refine ⟨true, ?_⟩
    rw [hcard]
    omega
