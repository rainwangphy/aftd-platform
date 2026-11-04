import AFTD.Prelude

/-!
# finite_three_weighted_sets_half_cover_implies_pair_cover

Topic: graphs   Node: de3256edb93a

Provenance: helper lemma. Elementary support observation in OP-337, motivated by https://arxiv.org/abs/2610.23487.

If a positive total of three nonnegative integer weights gives every point at least half the weight of the sets containing it, two of those sets cover every point.
-/

theorem finite_three_weighted_sets_half_cover_implies_pair_cover {α : Type*} [DecidableEq α]
    (A B C : Finset α) (x y z : ℕ)
    (hpos : 0 < x + y + z)
    (hcover : ∀ v : α, x + y + z ≤
      2 * ((if v ∈ A then x else 0) + (if v ∈ B then y else 0) +
        (if v ∈ C then z else 0))) :
    (∀ v, v ∈ A ∨ v ∈ B) ∨ (∀ v, v ∈ A ∨ v ∈ C) ∨
      (∀ v, v ∈ B ∨ v ∈ C) := by
  classical
  by_cases hAB : ∀ v, v ∈ A ∨ v ∈ B
  · exact Or.inl hAB
  by_cases hAC : ∀ v, v ∈ A ∨ v ∈ C
  · exact Or.inr (Or.inl hAC)
  by_cases hBC : ∀ v, v ∈ B ∨ v ∈ C
  · exact Or.inr (Or.inr hBC)
  push_neg at hAB hAC hBC
  obtain ⟨u,huA,huB⟩ := hAB
  obtain ⟨v,hvA,hvC⟩ := hAC
  obtain ⟨w,hwB,hwC⟩ := hBC
  have hu := hcover u
  have hv := hcover v
  have hw := hcover w
  simp only [huA,huB,if_false,zero_add] at hu
  simp only [hvA,hvC,if_false,zero_add,add_zero] at hv
  simp only [hwB,hwC,if_false,add_zero] at hw
  split_ifs at hu hv hw <;> omega
