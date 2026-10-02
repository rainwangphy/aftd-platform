import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsWalrasianEquilibrium

/-!
# walrasian_expenditure_ge_of_utility_ge

Topic: general_equilibrium   Node: d051a878b2ec

In a pure exchange economy E with finite agents Agent and finite, nonempty commodity type Good, if price vector p has strictly positive prices, agent i has a strictly monotone utility function, and (p, x) is a Walrasian equilibrium, then for any non-negative consumption bundle y such that agent i weakly prefers y to x_i (that is, E.utility i (x i) ≤ E.utility i y), the market expenditure on y is at least the value of agent i's initial endowment (that is, ∑ g, p g * E.endowment i g ≤ ∑ g, p g * y g).
-/

/-- Under strictly monotone utility and strictly positive prices, any non-negative bundle weakly preferred to the equilibrium bundle costs at least the endowment value. -/
theorem walrasian_expenditure_ge_of_utility_ge
    {Agent Good : Type*} [Fintype Agent] [Fintype Good] [Nonempty Good]
    (E : ExchangeEconomy Agent Good) (p : Good → ℝ) (x : Agent → Good → ℝ)
    (i : Agent)
    (hp : ∀ g, 0 < p g)
    (h_mono : StrictMono (E.utility i))
    (h_walras : is_walrasian_equilibrium E p x)
    (y : Good → ℝ) (hy_nonneg : ∀ g, 0 ≤ y g)
    (hy_u : E.utility i (x i) ≤ E.utility i y) :
    ∑ g, p g * E.endowment i g ≤ ∑ g, p g * y g := by
  have h_max := (h_walras.2 i).2
  by_contra! hlt
  set n : ℝ := (Fintype.card Good : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  set Δ := ∑ g, p g * E.endowment i g - ∑ g, p g * y g
  have hΔ : 0 < Δ := sub_pos.mpr hlt
  set c := Δ / n
  have hc : 0 < c := div_pos hΔ hn
  set z : Good → ℝ := fun g => y g + c / p g
  have hpz : ∀ g, p g * z g = p g * y g + c := by
    intro g
    dsimp [z]
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt (hp g))]
  have hsum : ∑ g, p g * z g = ∑ g, p g * E.endowment i g := by
    simp_rw [hpz, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.card : ℝ) = n := rfl
    rw [this, mul_div_cancel₀ _ (ne_of_gt hn)]
    exact add_sub_cancel _ _
  have hyz_gt : ∀ g, y g < z g := by
    intro g
    dsimp [z]
    have : 0 < c / p g := div_pos hc (hp g)
    linarith
  have hz_nonneg : ∀ g, 0 ≤ z g := by
    intro g
    exact le_trans (hy_nonneg g) (le_of_lt (hyz_gt g))
  have hyz_lt : y < z := by
    rw [lt_iff_le_and_ne]
    refine ⟨fun g => le_of_lt (hyz_gt g), ?_⟩
    intro h_eq
    obtain ⟨g0⟩ := ‹Nonempty Good›
    have h1 : y g0 = z g0 := congr_fun h_eq g0
    have h2 : y g0 < z g0 := hyz_gt g0
    linarith
  have h_util_lt : E.utility i y < E.utility i z := h_mono hyz_lt
  have h_util_le : E.utility i z ≤ E.utility i (x i) := h_max z hz_nonneg (le_of_eq hsum)
  linarith
