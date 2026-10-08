import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# empiricalStrategy

Topic: equilibria   Node: b1a4c67a60db

Provenance: formalization of a published result. Source: TCSlib, `empiricalStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given $T > 0$ pure actions $a_0, \dots, a_{T-1} \in \mathrm{Fin}\,n$, the
\emph{empirical strategy} is the mixed strategy assigning to each $i$ the
fraction of rounds on which action $i$ was played:
\[
  q_i \;=\; \frac{1}{T}\#\{t : a_t = i\}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The empirical distribution of a sequence of `T > 0` pure actions, as a mixed strategy: the weight of action `i` is the fraction of rounds in which `i` was played. This is the column player's final mixed strategy `Q̄` in the Hedge-vs-best-response interaction. [FS99, §5]. -/
noncomputable def empiricalStrategy {n T : ℕ} [NeZero n] (hT : 0 < T)
    (actions : Fin T → Fin n) : MixedStrategy n where
  weights i := (∑ t : Fin T, if actions t = i then (1 : ℝ) else 0) / T
  nonneg i := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun t _ => by split <;> positivity
    · exact Nat.cast_nonneg T
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    have hinner : ∀ t : Fin T, ∑ i : Fin n, (if actions t = i then (1 : ℝ) else 0) = 1 := by
      intro t
      rw [Finset.sum_eq_single (actions t)]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    simp_rw [hinner, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
