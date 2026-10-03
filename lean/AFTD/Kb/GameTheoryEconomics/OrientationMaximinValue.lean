import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RelevantMinValue

/-!
# orientation_maximin_value

Topic: fair_division   Node: 18c660019eae

The PROPm slack d_i: the maximum over other agents j of agent i's least value for a relevant edge held by j.
-/

/-- The PROPm slack `d_i = max_{j ≠ i} min { v_i(e) : e ∈ π_j ∩ E_i }` (Baklanov et al.'s maximin value, restricted to relevant items; `0` if no other agent holds a relevant item). -/
noncomputable def orientation_maximin_value {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (i : Fin n) : ℝ :=
  (Finset.univ.erase i).fold max 0 fun j => relevant_min_value ends u σ i j
