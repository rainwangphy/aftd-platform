import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op861_crossing_ordered_pairs_double

Topic: graphs   Node: 0d18f7877572

Provenance: helper lemma. Converts op861_ternary_crossing_pairs_dense to a lower bound on crossing-triangle graph edges.

In a linearly ordered abelian group of exponent three, the number of ordered pairs in a finite subset whose zero-sum third point lies outside the subset is twice the number of such pairs in increasing order.
-/

theorem op861_crossing_ordered_pairs_double (α : Type*) [AddCommGroup α]
    [DecidableEq α] [LinearOrder α] (h3 : ∀ t : α, t+t+t = 0) (S : Finset α) :
    ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card =
      2 * ((S.product S).filter (fun xy => xy.1 < xy.2 ∧ -(xy.1+xy.2) ∉ S)).card := by
  let A := (S.product S).filter (fun xy => xy.1 < xy.2 ∧ -(xy.1+xy.2) ∉ S)
  let B := (S.product S).filter (fun xy => xy.2 < xy.1 ∧ -(xy.1+xy.2) ∉ S)
  let E := (S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)
  change E.card = 2 * A.card
  have hAB_card : A.card = B.card := by
    refine Finset.card_bij' (fun xy _ => Prod.swap xy) (fun yx _ => Prod.swap yx) ?_ ?_ ?_ ?_
    · intro ⟨x, y⟩ h
      simp only [A, B, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Prod.swap] at h ⊢
      refine ⟨⟨h.1.2, h.1.1⟩, ?_⟩
      rw [add_comm]
      exact h.2
    · intro ⟨x, y⟩ h
      simp only [A, B, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Prod.swap] at h ⊢
      refine ⟨⟨h.1.2, h.1.1⟩, ?_⟩
      rw [add_comm]
      exact h.2
    · intro ⟨x, y⟩ _
      rfl
    · intro ⟨x, y⟩ _
      rfl
  have h_disj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro xy _ hA hB
    exact lt_asymm hA.1 hB.1
  have hE_eq : E = A ∪ B := by
    ext ⟨x, y⟩
    simp only [E, A, B, Finset.mem_filter, Finset.mem_union, Finset.product_eq_sprod, Finset.mem_product]
    constructor
    · rintro ⟨⟨hx, hy⟩, hneg⟩
      have hne : x ≠ y := by
        rintro rfl
        have h_neg_two : -(x + x) = x := neg_eq_of_add_eq_zero_right (h3 x)
        rw [h_neg_two] at hneg
        exact hneg hx
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨⟨hx, hy⟩, hlt, hneg⟩
      · exact Or.inr ⟨⟨hx, hy⟩, hgt, hneg⟩
    · rintro (⟨hxy, _, hneg⟩ | ⟨hxy, _, hneg⟩)
      · exact ⟨hxy, hneg⟩
      · exact ⟨hxy, hneg⟩
  rw [hE_eq, Finset.card_union_of_disjoint h_disj, hAB_card, two_mul]
