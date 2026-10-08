import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.Tcs.Regret

/-!
# regret_to_payoff

Topic: equilibria   Node: d672a523ead0

Provenance: helper lemma. TCSlib, `regret_to_payoff`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/FiniteMinimax.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Regret-to-payoff bridge for zero-sum games. Consider a finite two-player zero-sum game with $M \ge 1$ row actions and $N$ column
actions and payoff matrix $A$, every entry of which satisfies $0 \le A_{ij} \le 1$,
played over $T \ge 1$ rounds. Suppose that in each round $t$ the row player commits to a
probability distribution $p_t$ over the row actions (so $\sum_i p_t(i) = 1$) while the
column player chooses an action $j_t$, and that the cumulative loss regret is bounded by
$R$:
\[
  \sum_t \sum_i p_t(i)\,\bigl(1 - A_{i,j_t}\bigr)
  \;-\; \min_i \sum_t \bigl(1 - A_{i,j_t}\bigr) \;\le\; R,
\]
where the minimum runs over the row actions. Then the row player's cumulative expected
payoff satisfies
\[
  \sum_t \sum_i p_t(i)\,A_{i,j_t}
  \;\ge\;
  \max_i \sum_t A_{i,j_t} \;-\; R,
\]
with the maximum taken over the row actions.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The regret-to-payoff bridge: for `T` rounds in which the row player plays the distributions `p_t` (each summing to one) and the column player plays `j_t`, if the row player's loss regret on the losses `1 − A(i, j_t)` is at most `R`, i.e. `Σ_t Σ_i p_t(i) · (1 − A(i, j_t)) − inf_i Σ_t (1 − A(i, j_t)) ≤ R`, then the realized payoff sum satisfies `Σ_t Σ_i p_t(i) · A(i, j_t) ≥ sup_i Σ_t A(i, j_t) − R`. [CBL06, proof of Thm 7.1]; [FS99, §5]. Regret is stated for losses, but the game is stated in payoffs; since loss is `1 − payoff`, the learner's loss regret becomes a payoff guarantee against the best fixed row action in hindsight. **Proof sketch.** Step 1: since each `p_t` sums to one, the loss sum equals `T` minus the payoff sum. Step 2: the infimum over rows of `Σ_t (1 − A(i, j_t)) = T − Σ_t A(i, j_t)` equals `T` minus the supremum of the payoff sums (both directions of `le_antisymm`, using that the ranges are finite, hence bounded). Step 3: substituting Steps 1–2 into the hypothesis gives `sup_i Σ_t A(i, j_t) − Σ_t Σ_i p_t(i) A(i, j_t) ≤ R`. Step 4: the goal's supremum of `Σ_t A(i, j_t) − R` equals the supremum of the payoff sums minus `R` (the constant `R` does not depend on `i`); the claim then follows by linear arithmetic. -/
lemma regret_to_payoff {M N T : ℕ} [NeZero M] (G : ZeroSumGame M N) (_hT : 0 < T)
    (p : Fin T → Fin M → ℝ)
    (hp_sum : ∀ t, ∑ i : Fin M, p t i = 1)
    (j : Fin T → Fin N)
    (R : ℝ)
    (hregret : (∑ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t))) -
      ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (j t))) ≤ R) :
    ∑ t : Fin T, ∑ i : Fin M, p t i * G.payoff i (j t) ≥
      ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) - R := by
  -- Regret is stated for losses, but the game is stated in payoffs.  Since
  -- loss is `1 - payoff`, the learner's loss regret becomes a payoff guarantee
  -- against the best fixed row action in hindsight.
  -- Step 1: the loss sum is `T` minus the payoff sum.
  -- Rewrite the LHS of the hypothesis: ∑_t ∑_i p(t,i)*(1 - A(i,j_t)) = T - ∑_t ∑_i p(t,i)*A(i,j_t)
  have hlhs : ∑ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
      ↑T - ∑ t : Fin T, ∑ i : Fin M, p t i * G.payoff i (j t) := by
    have h_inner : ∀ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
        1 - ∑ i : Fin M, p t i * G.payoff i (j t) := by
      intro t
      have : ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
          ∑ i : Fin M, (p t i - p t i * G.payoff i (j t)) := by
        congr 1; ext i; ring
      rw [this, sum_sub_distrib, hp_sum]
    simp_rw [h_inner, Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Step 2: the infimum of `T − f` is `T` minus the supremum of `f`.
  -- Rewrite the iInf: ⨅_i ∑_t (1 - A(i,j_t)) = T - ⨆_i ∑_t A(i,j_t)
  have hrhs : ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (j t))) =
      ↑T - ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) := by
    have h_sum : ∀ i : Fin M, ∑ t : Fin T, (1 - G.payoff i (j t)) =
        ↑T - ∑ t : Fin T, G.payoff i (j t) := by
      intro i; simp [sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp_rw [h_sum]
    have hbdd_above : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t))) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hbdd_below : BddBelow
        (Set.range (fun i : Fin M => ↑T - ∑ t : Fin T, G.payoff i (j t))) :=
      Set.Finite.bddBelow (Set.finite_range _)
    apply le_antisymm
    · -- ⨅ i, (T - f i) ≤ T - ⨆ i, f i  ↔  ⨆ i, f i ≤ T - ⨅ i, (T - f i)
      have hsup : ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) ≤
          ↑T - ⨅ i : Fin M, (↑T - ∑ t : Fin T, G.payoff i (j t)) :=
        ciSup_le fun i => by linarith [ciInf_le hbdd_below i]
      linarith
    · exact le_ciInf fun i => by linarith [le_ciSup hbdd_above i]
  -- Step 3: substitute into the hypothesis.
  -- Now the hypothesis becomes (T - S_pay) - (T - S_max) ≤ R, so S_max - S_pay ≤ R
  rw [hlhs, hrhs] at hregret
  -- Step 4: pull the constant `R` out of the goal's supremum and conclude.
  -- The goal has ⨆ i, (∑ t, A(i,j_t) - R) which equals (⨆ i, ∑ t, A(i,j_t)) - R
  -- since R is constant w.r.t. i.
  rw [ge_iff_le]
  have hbdd_up : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t))) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hgoal_rw : ⨆ i : Fin M, (∑ t : Fin T, G.payoff i (j t) - R) =
      (⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t)) - R := by
    have hbdd : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t) - R)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    apply le_antisymm
    · apply ciSup_le; intro i
      linarith [le_ciSup hbdd_up i]
    · rw [sub_le_iff_le_add]
      apply ciSup_le; intro i
      have := le_ciSup hbdd i
      linarith
  rw [hgoal_rw]
  linarith
