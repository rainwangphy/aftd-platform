import AFTD.Prelude

/-!
# efx_locked_agent_values

Topic: fair_division   Node: 244ac1cc8111

Provenance: helper lemma. General locked-good projection for the OP-7 Pareto barrier; related three-agent instance arXiv:2002.05119 Section 5.

Extend n agents and m goods by a locked good and a new agent: original agents retain their old values and value the new good at one plus their total value for old goods; the new agent values each old good at 1 and the locked good at m+1.
-/

def efx_locked_agent_values {n m : ℕ} (v : Fin n → Fin m → ℝ) : Fin (n+1) → Fin (m+1) → ℝ := fun i g => Fin.lastCases (Fin.lastCases ((m : ℝ) + 1) (fun _ => (1 : ℝ)) g) (fun j => Fin.lastCases ((∑ h, v j h) + 1) (v j) g) i
