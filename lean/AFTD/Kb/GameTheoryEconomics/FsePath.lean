import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseSPAll
import AFTD.Kb.GameTheoryEconomics.FseLemmaC
import AFTD.Kb.GameTheoryEconomics.FseMix

/-!
# fse_path

Topic: mechanism_design   Node: 18044b54083f

Path lemma: if the outcome at c is v, and every coordinate in which z differs from c has c-value different from v, then the outcome at z is also v.
-/

/-- Path lemma: if the outcome at `c` is `v`, and every coordinate in which `z` differs from `c` has `c`-value different from `v`, then the outcome at `z` is also `v`. -/
lemma fse_path {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hSP : fse_SPAll f)
    (c z : Fin n → ℝ) (hc : fse_InDomain c) (hz : fse_InDomain z) (v : ℝ) (hv : f c = v)
    (hdiff : ∀ j, c j ≠ z j → c j ≠ v) : f z = v := by
  have hmixD : ∀ k, fse_InDomain (fse_mix c z k) := by
    intro k j; unfold fse_mix; split_ifs
    · exact hz j
    · exact hc j
  have key : ∀ k : ℕ, k ≤ n → f (fse_mix c z k) = v := by
    intro k
    induction k with
    | zero =>
      intro _
      have : fse_mix c z 0 = c := by funext j; simp [fse_mix]
      rw [this]; exact hv
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      set jk : Fin n := ⟨k, by omega⟩ with hjk
      have hupd : fse_mix c z (k + 1) = Function.update (fse_mix c z k) jk (z jk) := by
        funext j
        by_cases hj : j = jk
        · rw [hj, Function.update_self]; simp [fse_mix, hjk]
        · rw [Function.update_of_ne hj]
          have hne : j.val ≠ k := fun h => hj (Fin.ext (by simp [hjk, h]))
          simp only [fse_mix]
          by_cases hlt : j.val < k
          · simp [hlt, show j.val < k + 1 by omega]
          · simp [hlt, show ¬ j.val < k + 1 by omega]
      have hval : fse_mix c z k jk = c jk := by simp [fse_mix, hjk]
      by_cases hcz : c jk = z jk
      · have : fse_mix c z (k + 1) = fse_mix c z k := by
          rw [hupd, ← hcz, ← hval, Function.update_eq_self]
        rw [this]; exact ih'
      · have hne : f (fse_mix c z k) ≠ fse_mix c z k jk := by
          rw [ih', hval]; exact fun h => hdiff jk hcz h.symm
        rcases fse_lemmaC f hSP _ (hmixD k) jk (z jk) (hz jk) with h | h
        · exact absurd h hne
        · rw [hupd, h, ih']
  have hfin : fse_mix c z n = z := by
    funext j; simp [fse_mix, j.isLt]
  rw [← hfin]; exact key n le_rfl
