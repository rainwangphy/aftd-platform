import AFTD.Prelude

/-!
# parity_bound_counterexample_central_measurement

Topic: quantum   Node: f8ec6e7293ce

Provenance: helper lemma. step towards closed_network_parity_bound_qubits

A joint central measurement on ℂ^1 with outcome (0,0) certain: the POVM element M 0 0 is the 1×1 identity and all other elements vanish.
-/

/-- Joint central measurement on ℂ^1 concentrated on the outcome (0,0). -/
def parity_bound_counterexample_central_measurement : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := fun s0 s1 => if s0 = 0 ∧ s1 = 0 then 1 else 0
