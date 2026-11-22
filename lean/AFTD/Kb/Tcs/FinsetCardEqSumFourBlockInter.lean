import AFTD.Prelude
import AFTD.Kb.Tcs.FourDisjointSubsetsCardSumLe

/-!
# finset_card_eq_sum_four_block_inter

Topic: graphs   Node: eda8e5004be5

Provenance: helper lemma. OP-1957: graph-to-count transfer for the size-five block forced-edge route (IN-1126).

If four pairwise disjoint finite sets cover a finite type, every finite set has size equal to the sum of the sizes of its intersections with the four sets.
-/

theorem finset_card_eq_sum_four_block_inter {V : Type*} [Fintype V] [DecidableEq V] (A B C D P : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ) :
    P.card = (P ∩ A).card + (P ∩ B).card + (P ∩ C).card + (P ∩ D).card := by
  have hP : P ∩ A ∪ P ∩ B ∪ P ∩ C ∪ P ∩ D = P := by
    rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
      ← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
  have h := four_disjoint_subsets_card_sum_le (P ∩ A) (P ∩ B) (P ∩ C) (P ∩ D) P
    Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left
    Finset.inter_subset_left
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB))
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAC))
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAD))
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hBC))
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hBD))
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hCD))
  have h2 : P.card ≤ (P ∩ A).card + (P ∩ B).card + (P ∩ C).card + (P ∩ D).card := by
    calc P.card = (P ∩ A ∪ P ∩ B ∪ P ∩ C ∪ P ∩ D).card := by rw [hP]
      _ ≤ (P ∩ A ∪ P ∩ B ∪ P ∩ C).card + (P ∩ D).card := Finset.card_union_le _ _
      _ ≤ (P ∩ A ∪ P ∩ B).card + (P ∩ C).card + (P ∩ D).card := by
          have := Finset.card_union_le (P ∩ A ∪ P ∩ B) (P ∩ C); omega
      _ ≤ _ := by have := Finset.card_union_le (P ∩ A) (P ∩ B); omega
  omega
