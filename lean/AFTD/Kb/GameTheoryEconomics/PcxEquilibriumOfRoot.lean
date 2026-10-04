import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpVenueImpact
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoBestResponse
import AFTD.Kb.GameTheoryEconomics.PcxTheta
import AFTD.Kb.GameTheoryEconomics.PcxMu
import AFTD.Kb.GameTheoryEconomics.PcxCost
import AFTD.Kb.GameTheoryEconomics.PcxAssumptions
import AFTD.Kb.GameTheoryEconomics.PcxPoly
import AFTD.Kb.GameTheoryEconomics.PcxImpact
import AFTD.Kb.GameTheoryEconomics.PcxAction

/-!
# pcx_equilibrium_of_root

Topic: equilibria   Node: d9ebe2227a6e

Every positive root x of pcx_poly gives a pure-strategy equilibrium of the binary instance with impacts pcx_impact x, in which every type publishes a positive amount at every venue.
-/

open Finset in
/-- Every positive root of `pcx_poly` yields a pure-strategy equilibrium of the instance with venue impacts `pcx_impact x`, in which every type publishes a positive amount at every venue. -/
lemma pcx_equilibrium_of_root (x : ℝ) (hx : 0 < x) (hP : pcx_poly x = 0) :
    pcp_is_equilibrium (1 / 2) 2 pcx_theta pcx_mu pcx_cost (pcx_action x) (pcx_impact x) ∧
      ∀ i j, 0 < pcx_action x i j := by
  have h1 : (0 : ℝ) < 1 + 2 * x := by linarith
  have h2 : (0 : ℝ) < 1 + 512 * x := by linarith
  have h3 : (0 : ℝ) < 1 + 16 * x := by linarith
  have h4 : (0 : ℝ) < 1 + 4096 * x := by linarith
  set V1 := (1 + 16 * x) / (1 + 2 * x) with hV1
  set V2 := (1 + 4096 * x) / (1 + 512 * x) with hV2
  have hV1p : 0 < V1 := div_pos h3 h1
  have hV2p : 0 < V2 := div_pos h4 h2
  have hDL : ∑ l, pcx_impact x l ^ 4 / pcx_cost 0 l = V1 ^ 4 + V2 ^ 4 / 128 := by
    simp [Fin.sum_univ_two, pcx_impact, pcx_cost, hV1, hV2]
  have hDH : ∑ l, pcx_impact x l ^ 4 / pcx_cost 1 l = V1 ^ 4 + V2 ^ 4 / 8 := by
    simp [Fin.sum_univ_two, pcx_impact, pcx_cost, hV1, hV2]
  have hroot : V1 ^ 4 + V2 ^ 4 / 128 = x * (V1 ^ 4 + V2 ^ 4 / 8) := by
    have : x * (V1 ^ 4 + V2 ^ 4 / 8) - (V1 ^ 4 + V2 ^ 4 / 128) =
        pcx_poly x / ((1 + 2 * x) ^ 4 * (1 + 512 * x) ^ 4) := by
      rw [hV1, hV2, pcx_poly]; field_simp
    rw [hP, zero_div] at this; linarith
  have hDHp : 0 < V1 ^ 4 + V2 ^ 4 / 8 := by positivity
  have hSall : ∀ i, 0 < ∑ l, pcx_impact x l ^ 4 / pcx_cost i l :=
    Fin.forall_fin_two.mpr ⟨by rw [hDL]; positivity, by rw [hDH]; positivity⟩
  have hpos : ∀ i j, 0 < pcx_action x i j := by
    intro i j
    simp only [pcx_action]
    have hc : ∀ i j, 0 < pcx_cost i j := pcx_assumptions.1.2.2.2.2.2.1
    have hI : 0 < pcx_impact x j := by fin_cases j <;> simp [pcx_impact, hV1p, hV2p, ← hV1, ← hV2]
    have hS : 0 < ∑ l, pcx_impact x l ^ 4 / pcx_cost i l := hSall i
    have := hc i j
    positivity
  refine ⟨⟨?_, ?_⟩, hpos⟩
  · intro i
    have hc : ∀ j, 0 < pcx_cost i j := fun j => pcx_assumptions.1.2.2.2.2.2.1 i j
    have hS : 0 < ∑ l, pcx_impact x l ^ 4 / pcx_cost i l := hSall i
    exact pcp_half_two_best_response (pcx_cost i) (pcx_impact x) hc hS
  · intro j
    have hDL2 := hDL
    have hDH2 := hDH
    rw [Fin.sum_univ_two] at hDL2 hDH2
    simp only [pcp_venue_impact, pcx_action, Fin.sum_univ_two]
    rw [hDL2, hDH2, hroot]
    have hx0 : x ≠ 0 := hx.ne'
    fin_cases j
    · simp [pcx_impact, pcx_cost, pcx_mu, pcx_theta, ← hV1, ← hV2]
      field_simp
      simp only [hV1, hV2] at *
      field_simp
      try ring
    · simp [pcx_impact, pcx_cost, pcx_mu, pcx_theta, ← hV1, ← hV2]
      field_simp
      simp only [hV1, hV2] at *
      field_simp
      try ring
