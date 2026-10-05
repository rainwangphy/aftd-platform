import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaLhsSet
import AFTD.Kb.GameTheoryEconomics.GpaRhsSet
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaLhsIsGreatest
import AFTD.Kb.GameTheoryEconomics.GpaRhsIsGreatest

/-!
# gpa_eq54_fails_of_indep

Topic: mechanism_design   Node: a124e3e6157f

Eq. (5.4) of arXiv:2209.01146 (max_{Δ_k} (u* - h) = (1/k) max_{[0,1]^k} u*) fails on every graph whose independence number α satisfies 2 ≤ α < k: the two sides are 1 - 1/α + 1/k and α/k, and the first is strictly larger.
-/

open Finset in
/-- Eq. (5.4) of arXiv:2209.01146 (`max_{Δ_k} (u* - h) = (1/k) max_{[0,1]^k} u*`) fails on every graph whose independence number `α` satisfies `2 ≤ α < k`: the two sides are `1 - 1/α + 1/k` and `α/k`, and the first is strictly larger. -/
theorem gpa_eq54_fails_of_indep {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (I : Finset (Fin k)) (hI : gpa_indep G I) (hmax : ∀ S, gpa_indep G S → S.card ≤ I.card)
    (h2 : 2 ≤ I.card) (hk : I.card < k) (L R : ℝ)
    (hL : IsGreatest (gpa_lhsSet (gpa_adjMat G)) L)
    (hR : IsGreatest (gpa_rhsSet (gpa_adjMat G)) R) :
    R / (k : ℝ) < L := by
  have hL' := gpa_lhs_isGreatest G I hI hmax (by omega) hk.le
  have hR' := gpa_rhs_isGreatest G I hI hmax
  rw [hL.unique hL', hR.unique hR']
  have haR : (2 : ℝ) ≤ I.card := by exact_mod_cast h2
  have hkR : (I.card : ℝ) + 1 ≤ k := by exact_mod_cast hk
  have hapos : (0 : ℝ) < I.card := by linarith
  have hkpos : (0 : ℝ) < k := by linarith
  rw [div_lt_iff₀ hkpos]
  have e : (1 - 1 / (I.card : ℝ) + 1 / (k : ℝ)) * k
      = k - k / (I.card : ℝ) + 1 := by field_simp
  rw [e]
  -- need: a < k - k/a + 1, i.e. (a-1)(k-a) > 0 after multiplying by a
  rw [← sub_pos]
  have : (k : ℝ) - k / (I.card : ℝ) + 1 - I.card
      = ((I.card : ℝ) - 1) * ((k : ℝ) - I.card) / I.card := by field_simp; ring
  rw [this]
  apply div_pos _ hapos
  apply mul_pos <;> linarith
