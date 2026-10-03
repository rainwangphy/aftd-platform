import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IncidentEdges

/-!
# orientation_prop_share

Topic: fair_division   Node: 42dd2edd1c90

The proportional share of agent i in a multigraph orientation instance: half her value for her incident edges (each edge is relevant to two agents).
-/

/-- The refined proportional share of arXiv:2602.18098 (arXiv:2602.18098, §2.2), `PROP_i = Σ_{e ∈ E_i} v_i(e) / n_e`, specialised to (loopless) multigraphs where `n_e = 2`. -/
noncomputable def orientation_prop_share {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (u : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  additive_valuation (u i) (incident_edges ends i) / 2
