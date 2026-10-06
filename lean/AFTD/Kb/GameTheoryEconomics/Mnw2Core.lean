import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2Bracket
import AFTD.Kb.GameTheoryEconomics.Mnw2Case3

/-!
# mnw2_core

Topic: fair_division   Node: c93d73698214

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

Goods are grouped by their owners under an allocation O and an allocation N: A = (O:0, N:0), B = (O:1, N:0), C = (O:0, N:1), D = (O:1, N:1); agent 0 values the four groups p, q, r, s and agent 1 values them α, β, γ, δ. Assume both valuations are normalized (p + q + r + s = 1 = α + β + γ + δ) and that N's Nash welfare (p + q)(γ + δ) is at least that of five other allocations: O itself, (p + r)(β + δ); agent 0 gets A only, p(β + γ + δ); agent 0 gets C only, r(α + β + δ); agent 0 gets A∪B∪C, (p + q + r)δ; agent 0 gets A∪C∪D, (p + r + s)β. Then 23 (p + r + β + δ) ≤ 27 (p + q + γ + δ). If β ≤ q or r ≤ γ the bracket lemma applies; otherwise p ≤ γ + δ and δ ≤ p + q and a computer-found polynomial certificate finishes.
-/

/-- Core inequality of the two-agent price-of-MNW bound: five MNW constraints force 23 SW(O) ≤ 27 SW(N). -/
theorem mnw2_core (p q r s α β γ δ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (h1 : p + q + r + s = 1) (h2 : α + β + γ + δ = 1) (hO : (p + r) * (β + δ) ≤ (p + q) * (γ + δ)) (hA : p * (β + γ + δ) ≤ (p + q) * (γ + δ)) (hC : r * (α + β + δ) ≤ (p + q) * (γ + δ)) (hABC : (p + q + r) * δ ≤ (p + q) * (γ + δ)) (hACD : (p + r + s) * β ≤ (p + q) * (γ + δ)) : 23 * (p + r + β + δ) ≤ 27 * (p + q + γ + δ) := by
  by_cases hbq : β ≤ q
  · have hC' : r * (1 - γ) ≤ (p + q) * (γ + δ) := by
      have e : 1 - γ = α + β + δ := by linarith
      rw [e]; exact hC
    have hD' : r * δ ≤ (p + q) * γ := by linear_combination hABC
    have := mnw2_bracket (p + q) r γ δ (by linarith) hr hγ hδ (by linarith) hC' hD'
    linarith
  by_cases hrg : r ≤ γ
  · have hC' : β * (1 - q) ≤ (γ + δ) * (q + p) := by
      have e : 1 - q = p + r + s := by linarith
      rw [e]; linear_combination hACD
    have hD' : β * p ≤ (γ + δ) * q := by linear_combination hA
    have := mnw2_bracket (γ + δ) β q p (by linarith) hβ hq hp (by linarith) hC' hD'
    linarith
  rw [not_le] at hbq hrg
  have h3 : p ≤ γ + δ := by
    by_contra h
    rw [not_le] at h
    have e1 : (γ + δ) * β < p * β := mul_lt_mul_of_pos_right h (by linarith)
    have e2 : q * (γ + δ) ≤ β * (γ + δ) := mul_le_mul_of_nonneg_right hbq.le (by linarith)
    nlinarith
  have h4 : δ ≤ p + q := by
    by_contra h
    rw [not_le] at h
    have e1 : (p + q) * r < δ * r := mul_lt_mul_of_pos_right h (by linarith)
    have e2 : (p + q) * γ ≤ (p + q) * r := mul_le_mul_of_nonneg_left hrg.le (by linarith)
    nlinarith
  exact mnw2_case3 p q r s α β γ δ hp hq hr hs hα hβ hγ hδ h1 h2 h3 h4 hO hA hC hABC hACD
