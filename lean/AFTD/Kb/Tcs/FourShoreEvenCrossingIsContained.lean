import AFTD.Prelude
import AFTD.Kb.Tcs.FourShoreCrossingIntersectionAtLeastThree

/-!
# four_shore_even_crossing_is_contained

Topic: graphs   Node: 1b80824300c0

Provenance: helper lemma. OP-1957 four-shore crossing and repeated-shore analysis; scratch Lean axiom audit completed.

An even crossing with the saturated four-shore contains that entire shore.
-/

theorem four_shore_even_crossing_is_contained
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B W Q : Finset V)
    (hA : A ⊆ S) (hAcard : A.card = 4) (hBcard : B.card = 8)
    (hWQsize : W.card + Q.card = 12)
    (hcrossing : (A ∪ W).card + (B ∩ Q).card = 12)
    (hAW : (A ∩ W).Nonempty) (hAWeven : Even (A ∩ W).card)
    (hxB : x ∉ B) (hyB : y ∉ B) (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : A ⊆ W := by
  classical
  have hl := four_shore_crossing_intersection_at_least_three H x y hxy S A B W Q
    hA hAcard hBcard hWQsize hcrossing hAW hxB hyB hxQ hyQ hmax hSxy hBA hQW
  have hu : (A ∩ W).card ≤ 4 := by
    have hc := Finset.card_le_card (Finset.inter_subset_left : A ∩ W ⊆ A)
    omega
  obtain ⟨t,ht⟩ := hAWeven
  have hc : (A ∩ W).card = A.card := by omega
  have heq : A ∩ W = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  intro a ha
  have ha' : a ∈ A ∩ W := heq.symm ▸ ha
  exact (Finset.mem_inter.mp ha').2
