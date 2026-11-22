import AFTD.Prelude

/-!
# four_disjoint_subsets_card_sum_le

Topic: graphs   Node: 2ffbdf565f0a

Provenance: helper lemma. OP-1957: graph-to-count transfer for the size-five block forced-edge route (IN-1126).

Four pairwise disjoint subsets of a finite set have total size at most the size of that set.
-/

theorem four_disjoint_subsets_card_sum_le {V : Type*} [DecidableEq V] (s1 s2 s3 s4 T : Finset V)
    (h1 : s1 ⊆ T) (h2 : s2 ⊆ T) (h3 : s3 ⊆ T) (h4 : s4 ⊆ T)
    (d12 : Disjoint s1 s2) (d13 : Disjoint s1 s3) (d14 : Disjoint s1 s4)
    (d23 : Disjoint s2 s3) (d24 : Disjoint s2 s4) (d34 : Disjoint s3 s4) :
    s1.card + s2.card + s3.card + s4.card ≤ T.card := by
  have e1 : (s1 ∪ s2).card = s1.card + s2.card := Finset.card_union_of_disjoint d12
  have e2 : (s1 ∪ s2 ∪ s3).card = (s1 ∪ s2).card + s3.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d13, d23⟩)
  have e3 : (s1 ∪ s2 ∪ s3 ∪ s4).card = (s1 ∪ s2 ∪ s3).card + s4.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨d14, d24⟩, d34⟩)
  have hsub : s1 ∪ s2 ∪ s3 ∪ s4 ⊆ T :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset h1 h2) h3) h4
  have := Finset.card_le_card hsub
  omega
