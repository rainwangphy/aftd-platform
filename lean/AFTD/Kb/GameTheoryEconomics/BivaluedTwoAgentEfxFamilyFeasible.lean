import AFTD.Prelude

/-!
# bivalued_two_agent_efx_family_feasible

Topic: fair_division   Node: 8f9616e75de2

Provenance: helper lemma. arXiv:2610.14994 (Section 4.2, Theorem 4.1: two agents, scaled common-ratio bivalued goods admit an EFX, fPO and envy-freeable allocation)

EFX version of the two-agent common-ratio bivalued arithmetic. Goods are of four types LL, LH, HL, HH (worth (1,1), (1,r), (r,1), (r,r) to agents 0 and 1), n1..n4 of each; a, b, c, d of each type go to agent 0, inside one of the three weight-tie families (b = 0 and c = n3; a = b = d = 0; a = n1, c = n3, d = n4). EFX is written with the allowance L0 (resp. L1) equal to the value, to agent 0 (resp. 1), of the LEAST valuable good in the other agent's bundle (1 if that bundle holds a good the agent values at 1, else r if it is nonempty, else 0), so U1 <= U0 + L0 and V0 <= V1 + L1 say exactly that removing any one good from the other bundle removes the envy. The last conjunct is the subsidy aggregate 0 <= a0*(U0-U1) + a1*(V1-V0).
-/

/-- The two-agent common-ratio bivalued arithmetic with the EFX allowance taken at the least valuable good of the other bundle: some allocation from one of the three weight-tie families is EFX and satisfies the subsidy aggregate inequality. -/
def bivalued_two_agent_efx_family_feasible (n1 n2 n3 n4 : ℕ) (r a0 a1 : ℝ) : Prop := ∃ a b c d : ℕ, a ≤ n1 ∧ b ≤ n2 ∧ c ≤ n3 ∧ d ≤ n4 ∧
    ((b = 0 ∧ c = n3) ∨ (a = 0 ∧ b = 0 ∧ d = 0) ∨ (a = n1 ∧ c = n3 ∧ d = n4)) ∧
    (let U0 : ℝ := (a : ℝ) + (b : ℝ) + r * (c : ℝ) + r * (d : ℝ)
     let U1 : ℝ := ((n1 - a : ℕ) : ℝ) + ((n2 - b : ℕ) : ℝ) + r * ((n3 - c : ℕ) : ℝ)
       + r * ((n4 - d : ℕ) : ℝ)
     let V0 : ℝ := (a : ℝ) + r * (b : ℝ) + (c : ℝ) + r * (d : ℝ)
     let V1 : ℝ := ((n1 - a : ℕ) : ℝ) + r * ((n2 - b : ℕ) : ℝ) + ((n3 - c : ℕ) : ℝ)
       + r * ((n4 - d : ℕ) : ℝ)
     let L0 : ℝ := if (n1 - a) + (n2 - b) ≥ 1 then 1 else if (n3 - c) + (n4 - d) ≥ 1 then r else 0
     let L1 : ℝ := if a + c ≥ 1 then 1 else if b + d ≥ 1 then r else 0
     U1 ≤ U0 + L0 ∧ V0 ≤ V1 + L1 ∧ 0 ≤ a0 * (U0 - U1) + a1 * (V1 - V0))
