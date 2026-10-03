import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IncidentEdges

/-!
# relevant_min_value

Topic: fair_division   Node: 68bb252058de

Agent i's value for the least valuable of her relevant edges held by agent j, or 0 if j holds none.
-/

/-- Agent `i`'s value for the least valuable of her relevant items held by agent `j`, `min { v_i(e) : e ∈ π_j ∩ E_i }`, and `0` if agent `j` holds none of `i`'s relevant items. -/
noncomputable def relevant_min_value {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (i j : Fin n) : ℝ :=
  if h : (bundle_of σ j ∩ incident_edges ends i).Nonempty then
    (bundle_of σ j ∩ incident_edges ends i).inf' h (u i)
  else 0
