import AFTD.Prelude
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PmAnsFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv

/-!
# pm_rerank

Topic: algorithms   Node: 194d15c90127

Changing an alive element's rank to anything below n + #alive does not change any recorded answer (used both for the adversary's "kill" step and for the final fooling pair).
-/

/-- Changing an alive element's rank to anything below `n + #alive` does not change any recorded answer (used both for the adversary's "kill" step and for the final fooling pair). -/
theorem pm_rerank {n : ℕ} (S : PMState n) (hI : S.Inv) (c : Fin n → Bool)
    (hc : ∀ f ∈ S.facts, (c f.1 = c f.2.1 ↔ S.col f.1 = S.col f.2.1))
    (z : Fin n) (hz : z ∈ S.alive) (r : ℤ) (hr : r < (n : ℤ) + S.alive.card) :
    ∀ f ∈ S.facts, (pmFam c (Function.update S.rk z r)).ans f.1 f.2.1 =
      (pmFam c S.rk).ans f.1 f.2.1 := by
  obtain ⟨_, _, hI3, hI4, hI5, _, _⟩ := hI
  intro f hf
  obtain ⟨x, y, t⟩ := f
  simp only at hf ⊢
  have hzr : S.rk z < (n : ℤ) + S.alive.card := by
    rw [hI4 z hz]
    have : (z.val : ℤ) < n := by exact_mod_cast z.isLt
    have : (0 : ℤ) ≤ S.alive.card := by positivity
    linarith
  rw [pm_ans_fam, pm_ans_fam]
  by_cases hcol : c x = c y
  · by_cases hxy : x = y
    · subst hxy; simp
    have hold : S.col x = S.col y := (hc _ hf).1 hcol
    by_cases hx : x = z
    · subst hx
      have hy : y ∉ S.alive := fun hy => hI3 _ hf hz hy hxy hold
      have := hI5 y hy
      have hyz : y ≠ x := fun e => hxy e.symm
      simp [hyz, hcol]
      rw [if_pos (by linarith), if_pos (by linarith)]
    · by_cases hy : y = z
      · subst hy
        have hxa : x ∉ S.alive := fun hxa => hI3 _ hf hxa hz hxy hold
        have := hI5 x hxa
        simp [hx, hcol]
        rw [if_neg (by linarith), if_pos (by linarith), if_neg (by linarith),
          if_pos (by linarith)]
      · simp [Function.update_apply, hx, hy]
  · have hcol' : ¬ c y = c x := fun e => hcol e.symm
    simp [hcol, hcol']
