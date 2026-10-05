import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseIsScaling
import AFTD.Kb.GameTheoryEconomics.FseSPAll

/-!
# fse_lemmaC

Topic: mechanism_design   Node: f12dad7474f5

Key consequence of strategyproofness for all scaling functions: a unilateral deviation can change the outcome only if the outcome was at the deviator's own location.
-/

/-- Key consequence of strategyproofness for all scaling functions: a unilateral deviation can change the outcome only if the outcome was at the deviator's own location. -/
lemma fse_lemmaC {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hSP : fse_SPAll f)
    (x : Fin n → ℝ) (hx : fse_InDomain x) (i : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f x = x i ∨ f (Function.update x i t) = f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set y := f x with hy
  set y' := f (Function.update x i t) with hy'
  have hyy : 0 < |y - y'| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h2))
  have hxy : 0 < |x i - y| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h1))
  have hden : 0 < |x i - y'| + 1 := by positivity
  set δ := |y - y'| * |x i - y| / (|x i - y'| + 1) with hδ
  have hδpos : 0 < δ := div_pos (mul_pos hyy hxy) hden
  have hδeq : δ * (|x i - y'| + 1) = |y - y'| * |x i - y| := by
    rw [hδ]; field_simp
  let q : ℝ → ℝ := fun z => |z - y'| + δ
  have hq : fse_IsScaling q := by
    refine ⟨?_, ?_⟩
    · exact (Continuous.continuousOn (by fun_prop))
    · intro z _; positivity
  have := hSP q hq x hx i t ht
  simp only [fse_cost, q] at this
  rw [← hy, ← hy', sub_self, abs_zero, zero_add] at this
  nlinarith [abs_nonneg (x i - y'), abs_nonneg (y - y')]
