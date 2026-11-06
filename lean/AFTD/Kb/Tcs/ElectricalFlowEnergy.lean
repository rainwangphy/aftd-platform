import AFTD.Prelude

/-!
# electrical_flow_energy

Topic: online_algorithms   Node: 5be744cd17fe

Provenance: formalization of a published result. Source: arXiv:2611.05669, Section 4.1

Given resistance values d on pairs in Fin k and a flow F : Fin k → Fin k → ℝ, the electrical energy of F is the sum ∑ i, ∑ j with i < j, d i j * (F i j)^2.
-/

/-- The quadratic electrical energy of a flow F with edge resistances d. -/
def electrical_flow_energy {k : ℕ} (d : Fin k → Fin k → ℝ) (F : Fin k → Fin k → ℝ) : ℝ := ∑ i : Fin k, ∑ j with i < j, d i j * (F i j) ^ 2
