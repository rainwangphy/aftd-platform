import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpVenueImpact
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoBestResponse
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoAction
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoActionSmul

/-!
# pcp_two_venue_equilibrium_of_fixed_point

Topic: equilibria   Node: c1f8733f6541

Two venues, alpha = 1/2, beta = 2, any number of types: if the impacts u induced by best responses to the normalised impacts (1, y) satisfy u_0 > 0 and u_1 = y u_0, then (u_0, u_1) with the closed-form actions is a pure-strategy equilibrium.
-/

open Finset in
/-- Two venues, `α = 1/2`, `β = 2`, any number of types: let `u` be the venue impacts induced by the closed-form actions against the normalised impacts `(1, y)`. If `u 0 > 0` and `u 1 = y * u 0`, then the impacts `(u 0, u 1)` together with the closed-form actions against them form a pure-strategy equilibrium. -/
lemma pcp_two_venue_equilibrium_of_fixed_point {n : ℕ} (θ μ : Fin n → ℝ) (c : Fin n → Fin 2 → ℝ)
    (hc : ∀ i j, 0 < c i j) (y : ℝ)
    (hu0 : 0 < pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 0)
    (hfix : pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 1 =
      y * pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 0) :
    pcp_is_equilibrium (1 / 2) 2 θ μ c
      (pcp_half_two_action c ![pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 0,
        pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 1])
      ![pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 0,
        pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) 1] := by
  set u := pcp_venue_impact θ μ (pcp_half_two_action c ![1, y]) with hu
  have hv : (![u 0, u 1] : Fin 2 → ℝ) = fun j => u 0 * (![1, y] : Fin 2 → ℝ) j := by
    funext j; fin_cases j
    · simp
    · simp [hfix, mul_comm]
  have ha : pcp_half_two_action c ![u 0, u 1] = pcp_half_two_action c ![1, y] := by
    rw [hv, pcp_half_two_action_smul _ _ hu0.ne']
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have hD : 0 < ∑ l, (![u 0, u 1] : Fin 2 → ℝ) l ^ 4 / c i l := by
      rw [Fin.sum_univ_two]
      have h0 := hc i 0
      have h1 := hc i 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      positivity
    exact pcp_half_two_best_response (c i) _ (hc i) hD
  · rw [ha, hu]; fin_cases j <;> rfl
