import AFTD.Prelude

/-!
# fse_exists_avoid

Topic: mechanism_design   Node: 690b7ba6e63b

Some point of [0,1] avoids any given finite set.
-/

/-- Some point of `[0,1]` avoids any given finite set. -/
lemma fse_exists_avoid (S : Set ℝ) (hS : S.Finite) : ∃ e ∈ Set.Icc (0 : ℝ) 1, e ∉ S := by
  obtain ⟨e, he1, he2⟩ := ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).sdiff hS).nonempty
  exact ⟨e, he1, he2⟩
