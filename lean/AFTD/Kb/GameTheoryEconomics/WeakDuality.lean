import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# weak_duality

Topic: equilibria   Node: 21f9e1182664

Provenance: helper lemma. TCSlib, `weak_duality`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weak duality for finite zero-sum games. Let $G$ be a finite two-player zero-sum game with $M \ge 1$ row actions and $N \ge 1$
column actions, given by a payoff matrix $A$ whose entries satisfy $A_{ij} \in [0,1]$,
where the row player maximises and the column player minimises. Let $p = (p_i)$ be a
mixed strategy for the row player and $q = (q_j)$ a mixed strategy for the column
player. Then the row player's guaranteed payoff under $p$ never exceeds the payoff the
column player can be forced above under $q$:
\[
  \min_{j} \sum_{i} p_i\, A_{ij} \;\le\; \max_{i} \sum_{j} A_{ij}\, q_j .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Weak duality: for any row mixed strategy `p` and column mixed strategy `q`, the infimum over pure columns `j` of the payoff of `p` against `j` is at most the supremum over pure rows `i` of the payoff of `i` against `q`. [CBL06, §7.2 (the trivial direction `max min ≤ min max`)]; [FS99, §2]. **Proof sketch.** Let `v := Σᵢ Σⱼ pᵢ A(i, j) qⱼ` be the bilinear expected payoff of `(p, q)`. Step 1: writing `v = Σⱼ payoff(p, j) · qⱼ` as a `q`-average over columns and bounding each term below by the column infimum (which is bounded below by `0`) gives `inf_j payoff(p, j) ≤ v`. Step 2: writing `v = Σᵢ payoff(i, q) · pᵢ` as a `p`-average over rows and bounding each term above by the row supremum (bounded above by `1`) gives `v ≤ sup_i payoff(i, q)`. Chain the two. -/
theorem weak_duality {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (q : MixedStrategy N) :
    (⨅ j : Fin N, payoffVsPure G p j) ≤ ⨆ i : Fin M, pureVsPayoff G i q := by
  -- Put the bilinear expected payoff in the middle.  It is at least the worst
  -- pure-column payoff against `p`, and at most the best pure-row payoff
  -- against `q`.
  set v := ∑ i : Fin M, ∑ j : Fin N, p.weights i * G.payoff i j * q.weights j
  -- Step 1: the column infimum is at most `v` (average of `v` over columns).
  have hv_lb : ⨅ j, payoffVsPure G p j ≤ v := by
    -- Rewrite `v` as an average over columns and compare each term to the
    -- column infimum.
    have hv_eq : v = ∑ j : Fin N, payoffVsPure G p j * q.weights j := by
      simp only [v, payoffVsPure]; rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    rw [hv_eq]
    have hbdd : BddBelow (Set.range (payoffVsPure G p)) :=
      ⟨0, by rintro _ ⟨j, rfl⟩; exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (p.nonneg i) (G.payoff_nonneg i j)⟩
    calc ⨅ j, payoffVsPure G p j
        = (⨅ j, payoffVsPure G p j) * ∑ j, q.weights j := by rw [q.sum_one, mul_one]
      _ = ∑ j, (⨅ j, payoffVsPure G p j) * q.weights j := Finset.mul_sum ..
      _ ≤ ∑ j, payoffVsPure G p j * q.weights j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (ciInf_le hbdd j) (q.nonneg j)
  -- Step 2: `v` is at most the row supremum (average of `v` over rows).
  have hv_ub : v ≤ ⨆ i, pureVsPayoff G i q := by
    -- Rewrite `v` as an average over rows and compare each term to the row
    -- supremum.
    have hv_eq : v = ∑ i : Fin M, pureVsPayoff G i q * p.weights i := by
      simp only [v, pureVsPayoff]; simp_rw [Finset.sum_mul]
      congr 1; ext i; congr 1; ext j; ring
    rw [hv_eq]
    have hbdd : BddAbove (Set.range (pureVsPayoff G · q)) :=
      ⟨1, by rintro _ ⟨i, rfl⟩
             calc ∑ j : Fin N, G.payoff i j * q.weights j
                 ≤ ∑ j : Fin N, 1 * q.weights j :=
                   Finset.sum_le_sum fun j _ =>
                     mul_le_mul_of_nonneg_right (G.payoff_le_one i j) (q.nonneg j)
               _ = 1 := by simp [q.sum_one]⟩
    calc ∑ i, pureVsPayoff G i q * p.weights i
        ≤ ∑ i, (⨆ i, pureVsPayoff G i q) * p.weights i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (le_ciSup hbdd i) (p.nonneg i)
      _ = (⨆ i, pureVsPayoff G i q) := by
          rw [← Finset.mul_sum]; rw [p.sum_one, mul_one]
  linarith
