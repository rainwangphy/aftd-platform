import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistribution
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# empiricalJoint

Topic: equilibria   Node: 0af66ad25fb7

Provenance: formalization of a published result. Source: TCSlib, `empiricalJoint`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given $T > 0$ rounds of play in which the row player uses mixed strategy $p_t$
and the column player uses $q_t$, the empirical joint distribution assigns to
each profile $(i,j)$ the time-averaged probability
$\frac{1}{T}\sum_{t=1}^{T} (p_t)_i \cdot (q_t)_j$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The empirical joint distribution of `T > 0` rounds in which the row player plays the mixed strategy `p t` and the column player plays the mixed strategy `q t`, drawing their actions independently: the profile `(i, j)` has probability `(1/T) Σ_t p_t(i) · q_t(j)`. [Rou13-L17, §3 (time-averaged history `σ`)]. **Proof sketch** (that the mass is one). Each round contributes a product distribution of total mass one (`h_round_sum`, by summing out `q t` and then `p t`); pull the division by `T` out of the double sum (`hPullDiv`), swap the time sum to the outside (`hSwap`), and the total is `T · 1 / T = 1`. -/
noncomputable def empiricalJoint {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) :
    JointDistribution M N where
  prob i j := (∑ t : Fin T, (p t).weights i * (q t).weights j) / T
  nonneg i j := div_nonneg
    (Finset.sum_nonneg fun t _ => mul_nonneg ((p t).nonneg i) ((q t).nonneg j))
    (Nat.cast_nonneg T)
  sum_one := by
    -- Each round contributes a product distribution of total mass one, so the
    -- time average also has total mass one.
    have hT_ne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT)
    have h_round_sum : ∀ t : Fin T,
        ∑ i : Fin M, ∑ j : Fin N, (p t).weights i * (q t).weights j = 1 := by
      intro t
      calc ∑ i : Fin M, ∑ j : Fin N, (p t).weights i * (q t).weights j
          = ∑ i : Fin M, (p t).weights i * ∑ j : Fin N, (q t).weights j := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.mul_sum]
        _ = ∑ i : Fin M, (p t).weights i * 1 := by rw [(q t).sum_one]
        _ = 1 := by simp [(p t).sum_one]
    have hPullDiv :
        ∑ i : Fin M, ∑ j : Fin N,
            (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
          (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
              (p t).weights i * (q t).weights j) / (T : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    have hSwap :
        (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
            (p t).weights i * (q t).weights j) =
          ∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
              (p t).weights i * (q t).weights j := by
      rw [show (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
                (p t).weights i * (q t).weights j) =
            (∑ i : Fin M, ∑ t : Fin T, ∑ j : Fin N,
                (p t).weights i * (q t).weights j) from
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
      exact Finset.sum_comm
    rw [hPullDiv, hSwap]
    simp_rw [h_round_sum]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self hT_ne
