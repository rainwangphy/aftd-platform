import AFTD.Prelude
import AFTD.Kb.Tcs.ElectricalFlowEnergy
import AFTD.Kb.Tcs.IsFeasibleFlow

/-!
# electrical_energy

Topic: online_algorithms   Node: 3b40ac3cf89e

Provenance: formalization of a published result. Source: arXiv:2611.05669, Section 4.1

The electrical energy E(a) of a demand vector a : Fin k → ℝ with respect to resistances d is the infimum of the flow energies electrical_flow_energy d F over all feasible flows F for a.
-/

/-- The minimum electrical energy of a demand vector a with resistances d. -/
noncomputable def electrical_energy {k : ℕ} (d : Fin k → Fin k → ℝ) (a : Fin k → ℝ) : ℝ := sInf { electrical_flow_energy d F | (F : Fin k → Fin k → ℝ) (_ : is_feasible_flow F a) }
