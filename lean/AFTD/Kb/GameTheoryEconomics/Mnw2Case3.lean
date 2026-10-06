import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2Case3DenomPos
import AFTD.Kb.GameTheoryEconomics.Mnw2Case3Key

/-!
# mnw2_case3

Topic: fair_division   Node: 82d814de2836

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

Goods are grouped by their owners under an allocation O and an allocation N: A = (O:0, N:0), B = (O:1, N:0), C = (O:0, N:1), D = (O:1, N:1); agent 0 values the four groups p, q, r, s and agent 1 values them α, β, γ, δ. If p ≤ γ + δ, δ ≤ p + q, the valuations are normalized, and the five MNW constraints (N beats O and the allocations giving agent 0 exactly A, C, A∪B∪C, A∪C∪D) hold, then 23 SW(O) ≤ 27 SW(N), where SW(O) = p + r + β + δ and SW(N) = p + q + γ + δ.
-/

/-- The hard case (p ≤ γ + δ and δ ≤ p + q) of the two-agent price-of-MNW core inequality. -/
theorem mnw2_case3 (p q r s α β γ δ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (h1 : p + q + r + s = 1) (h2 : α + β + γ + δ = 1) (h3 : p ≤ γ + δ) (h4 : δ ≤ p + q) (hO : (p + r) * (β + δ) ≤ (p + q) * (γ + δ)) (hA : p * (β + γ + δ) ≤ (p + q) * (γ + δ)) (hC : r * (α + β + δ) ≤ (p + q) * (γ + δ)) (hABC : (p + q + r) * δ ≤ (p + q) * (γ + δ)) (hACD : (p + r + s) * β ≤ (p + q) * (γ + δ)) : 23 * (p + r + β + δ) ≤ 27 * (p + q + γ + δ) := by
  obtain ⟨e3, he3n, he3⟩ : ∃ e : ℝ, 0 ≤ e ∧ e = γ + δ - p := ⟨_, by linarith, rfl⟩
  obtain ⟨e4, he4n, he4⟩ : ∃ e : ℝ, 0 ≤ e ∧ e = p + q - δ := ⟨_, by linarith, rfl⟩
  have hM := mnw2_case3_denom_pos p q r s α β γ δ e3 e4 hp hq hr hs hα hβ hγ hδ he3n he4n
  have key := mnw2_case3_key p q r s α β γ δ e3 e4 hp hq hr hs hα hβ hγ hδ he3n he4n h1 h2 he3 he4
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hM).mp key)
