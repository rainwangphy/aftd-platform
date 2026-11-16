import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PreferenceWithUniqueTop

/-!
# exists_preference_with_unique_top

Topic: social_choice   Node: a99fa05f5b29

Provenance: helper lemma. folklore

For every alternative p in X, there exists a preference relation with unique top p.
-/

/-- For every alternative, there exists a preference relation with that alternative as unique top. -/
theorem exists_preference_with_unique_top {X : Type*} (p : X) : ∃ R : PreferenceWithUniqueTop X, R.top = p := by
  refine ⟨⟨fun x y => x = p ∨ y ≠ p, ?_, ?_, p, ?_⟩, rfl⟩
  · intro x y
    by_cases hx : x = p
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · intro x y z hxy hyz
    rcases hxy with hx | hy
    · exact Or.inl hx
    · rcases hyz with hy' | hz
      · exact (hy hy').elim
      · exact Or.inr hz
  · intro y hy h
    rcases h with h1 | h2
    · exact hy h1
    · exact h2 rfl
