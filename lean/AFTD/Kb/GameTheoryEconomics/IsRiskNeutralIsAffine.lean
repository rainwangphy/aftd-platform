import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsRiskNeutral
import AFTD.Kb.GameTheoryEconomics.IsAffineUtility
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.GameTheoryEconomics.LotteryPure
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValueMix
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValuePure
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# IsRiskNeutral.isAffine

Topic: general_equilibrium   Node: f297b9d2c0ef

Provenance: formalization of a published result. Source: EconCSLib, `IsRiskNeutral.isAffine`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Risk neutrality implies affine utility. [MSZ 2.27, hard direction] Requires `|I| ≥ 2` so that non-trivial distributions exist.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- Risk neutrality implies affine utility. [MSZ 2.27, hard direction] Requires `|I| ≥ 2` so that non-trivial distributions exist. -/
theorem IsRiskNeutral.isAffine {I : Type*} [Fintype I] [Nontrivial I] {u : 𝕜 → 𝕜}
    (h : IsRiskNeutral (I := I) u) : IsAffineUtility u := by
  classical
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne I
  -- Step 1: derive convex combination property from risk neutrality
  -- u(t·a + (1-t)·b) = t·u(a) + (1-t)·u(b) for t ∈ [0,1]
  have conv : ∀ (t : 𝕜) (_ : 0 ≤ t) (_ : t ≤ 1) (a b : 𝕜),
      u (t * a + (1 - t) * b) = t * u a + (1 - t) * u b := by
    intro t ht₀ ht₁ a b
    let p := Lottery.mix t ht₀ ht₁ (Lottery.pure (𝕜 := 𝕜) i₀) (Lottery.pure i₁)
    let f : I → 𝕜 := fun i => if i = i₀ then a else b
    have hL : wsum p f = t * a + (1 - t) * b := by
      change Lottery.expectedValue p f = _
      rw [Lottery.expectedValue_mix]
      simp [Lottery.expectedValue_pure, f, hne.symm]
    have hR : wsum p (u ∘ f) = t * u a + (1 - t) * u b := by
      change Lottery.expectedValue p (u ∘ f) = _
      rw [Lottery.expectedValue_mix]
      simp [Lottery.expectedValue_pure, Function.comp, f, hne.symm]
    rw [← hL, h p f, hR]
  -- Step 2: u(x) = (u 1 - u 0) · x + u 0 for all x
  refine ⟨u 1 - u 0, u 0, fun x => ?_⟩
  -- Case x ∈ [0,1]: u(x·1 + (1-x)·0) = x·u(1) + (1-x)·u(0)
  -- Case x > 1: u((1/x)·x + (1-1/x)·0) = (1/x)·u(x) + (1-1/x)·u(0), solve for u(x)
  -- Case x < 0: u(0) = (1/2)·u(x) + (1/2)·u(-x), with u(-x) known since -x > 0
  suffices ∀ y : 𝕜, 0 ≤ y → u y = (u 1 - u 0) * y + u 0 by
    by_cases hx : 0 ≤ x
    · exact this x hx
    · push_neg at hx
      have hmx := this (-x) (le_of_lt (neg_pos.mpr hx))
      have h_mid := conv (1 / 2) (by norm_num) (by norm_num) x (-x)
      have : (1 : 𝕜) / 2 * x + (1 - 1 / 2) * -x = 0 := by ring
      rw [this] at h_mid
      linarith
  intro y hy
  rcases eq_or_lt_of_le hy with rfl | hy_pos
  · simp
  rcases le_or_gt y 1 with hy1 | hy1
  · -- y ∈ (0, 1]
    have := conv y hy hy1 1 0
    simp at this; linarith
  · -- y > 1
    have h_inv := conv (1 / y) (le_of_lt (div_pos one_pos hy_pos))
      ((div_le_one hy_pos).mpr (le_of_lt hy1)) y 0
    simp at h_inv
    have hyne : y ≠ 0 := ne_of_gt hy_pos
    field_simp at h_inv ⊢; linarith
