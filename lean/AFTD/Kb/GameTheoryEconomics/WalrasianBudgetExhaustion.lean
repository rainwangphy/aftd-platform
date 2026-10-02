import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsWalrasianEquilibrium

/-!
# walrasian_budget_exhaustion

Topic: general_equilibrium   Node: ebb2c6564644

In a pure exchange economy E with finite agents Agent and finite, nonempty commodity type Good, if price vector p has strictly positive prices, agent i has a strictly monotone utility function, and (p, x) is a Walrasian equilibrium, then agent i exhausts their budget at equilibrium: the expenditure on allocation x_i equals the value of agent i's initial endowment (that is, ∑ g, p g * x i g = ∑ g, p g * E.endowment i g).
-/

/-- At a Walrasian equilibrium with strictly positive prices and strictly monotone preferences, every agent's budget constraint binds with equality. -/
theorem walrasian_budget_exhaustion
    {Agent Good : Type*} [Fintype Agent] [Fintype Good] [Nonempty Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (i : Agent)
    (hp : ∀ g, 0 < p g)
    (h_mono : StrictMono (E.utility i))
    (h_walras : is_walrasian_equilibrium E p x) :
    ∑ g, p g * x i g = ∑ g, p g * E.endowment i g := by
  have h_le := (h_walras.2 i).1
  have h_max := (h_walras.2 i).2
  have h_feas_nonneg := h_walras.1.1 i
  apply le_antisymm h_le
  by_contra! hlt
  set n : ℝ := (Fintype.card Good : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  set Δ := ∑ g, p g * E.endowment i g - ∑ g, p g * x i g
  have hΔ : 0 < Δ := sub_pos.mpr hlt
  set c := Δ / n
  have hc : 0 < c := div_pos hΔ hn
  set y : Good → ℝ := fun g => x i g + c / p g
  have hpy : ∀ g, p g * y g = p g * x i g + c := by
    intro g
    dsimp [y]
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt (hp g))]
  have hsum : ∑ g, p g * y g = ∑ g, p g * E.endowment i g := by
    simp_rw [hpy, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.card : ℝ) = n := rfl
    rw [this, mul_div_cancel₀ _ (ne_of_gt hn)]
    exact add_sub_cancel _ _
  have hy_gt : ∀ g, x i g < y g := by
    intro g
    dsimp [y]
    have : 0 < c / p g := div_pos hc (hp g)
    linarith
  have hy_nonneg : ∀ g, 0 ≤ y g := by
    intro g
    exact le_trans (h_feas_nonneg g) (le_of_lt (hy_gt g))
  have hxy_lt : x i < y := by
    rw [lt_iff_le_and_ne]
    refine ⟨fun g => le_of_lt (hy_gt g), ?_⟩
    intro h_eq
    obtain ⟨g0⟩ := ‹Nonempty Good›
    have h1 : x i g0 = y g0 := congr_fun h_eq g0
    have h2 : x i g0 < y g0 := hy_gt g0
    linarith
  have h_util_lt : E.utility i (x i) < E.utility i y := h_mono hxy_lt
  have h_util_le : E.utility i y ≤ E.utility i (x i) := h_max y hy_nonneg (le_of_eq hsum)
  exact not_le_of_gt h_util_lt h_util_le
