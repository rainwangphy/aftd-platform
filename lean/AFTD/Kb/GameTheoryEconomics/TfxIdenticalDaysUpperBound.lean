import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxAlphaTEFX
import AFTD.Kb.GameTheoryEconomics.TfxVal
import AFTD.Kb.GameTheoryEconomics.TfxNoAlphaTEFX

/-!
# tfx_identical_days_upper_bound

Topic: fair_division   Node: ca9fbbe5bfde

Identical days, two agents: no α-TEFX guarantee beyond 1/√2. For every α > √2/2 there is an identical-days instance with two agents having identical non-negative additive valuations (three goods per round, worth 0, 1 and 2 + 2√2, over three rounds) that admits no α-TEFX allocation. Hence the best approximation ratio for TEFX under identical days with two agents (open question of arXiv 2607.17224, Section 7; the paper proves 1/2 is achievable) is at most 1/√2.
-/

/-- **Identical days, two agents: no `α`-TEFX guarantee beyond `1/√2`.** For every `α > √2/2` there is an identical-days instance with two agents having identical non-negative additive valuations (three goods per round, worth `0`, `1` and `2 + 2√2`, over three rounds) that admits no `α`-TEFX allocation. Hence the best approximation ratio for TEFX under identical days with two agents (open question of arXiv 2607.17224, Section 7; the paper proves `1/2` is achievable) is at most `1/√2`. -/
theorem tfx_identical_days_upper_bound (α : ℝ) (hα : Real.sqrt 2 / 2 < α) :
    ∃ v : Fin 2 → Fin 3 → ℝ, (∀ i g, 0 ≤ v i g) ∧ (∀ i, v i = v 0) ∧
      ∀ σ : Fin 3 → Fin 3 → Fin 2, ¬ tfx_alphaTEFX α v σ := by
  set s := Real.sqrt 2 with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hα0 : 0 < α := lt_trans (by positivity) hα
  refine ⟨tfx_val (2 + 2 * s), ?_, fun _ => rfl, ?_⟩
  · intro i g
    fin_cases g <;> simp [tfx_val] <;> positivity
  · intro σ
    apply tfx_no_alphaTEFX α (2 + 2 * s) hα0 (by positivity)
    · nlinarith [mul_pos (sub_pos.mpr hα) (by positivity : (0:ℝ) < 2 + 2 * s)]
    · nlinarith [mul_pos (sub_pos.mpr hα) (by positivity : (0:ℝ) < 4 + 4 * s)]
    · nlinarith [mul_pos (sub_pos.mpr hα) (by positivity : (0:ℝ) < 4 + 2 * s)]
