import AFTD.Prelude

/-!
# sum_range_getD_append

Topic: mechanism_design   Node: 097307f1d8b8

Summing the first |mine| entries of mine ++ others gives the sum of mine.
-/

lemma sum_range_getD_append (mine others : List ℝ) :
    ∑ j ∈ Finset.range mine.length, (mine ++ others).getD j 0 = mine.sum := by
  induction mine with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring
