import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseDictatorship
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseLeftmostLe

/-!
# fse_leftmost_not_dictatorship

Topic: mechanism_design   Node: a33dbc5a9cdf

With at least two agents the leftmost mechanism is not a dictatorship.
-/

/-- With at least two agents the leftmost mechanism is not a dictatorship. -/
lemma fse_leftmost_not_dictatorship {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ¬ fse_Dictatorship (fse_leftmost (n := n)) := by
  rintro ⟨i, hi⟩
  -- another agent `j ≠ i`
  obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
    by_cases h : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro hc; rw [← hc] at h; simp at h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro hc; rw [← hc] at h; simp at h
  let x : Fin n → ℝ := fun k => if k = i then 1 else 0
  have hx : fse_InDomain x := by
    intro k; by_cases hk : k = i <;> simp [x, hk]
  have h1 := hi x hx
  have h2 := fse_leftmost_le x j
  simp only [x, if_neg hji, if_pos rfl] at h1 h2
  linarith
