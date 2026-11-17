import AFTD.Prelude
import AFTD.Kb.Tcs.TensorProdEndNodes

/-!
# closed_network_correlator_I

Topic: quantum   Node: 3f9d56332d8f

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 8

Given n, d, m : ℕ, end-node observables B : Fin n → Fin 2 → Matrix (Fin d) (Fin d) ℂ, central observable F0 : Matrix (Fin m) (Fin m) ℂ, and state ρ : Matrix ((Fin n → Fin d) × Fin m) ((Fin n → Fin d) × Fin m) ℂ, closed_network_correlator_I n d m B F0 ρ is (1 / 2 : ℝ) ^ n * ∑ y : Fin n → Fin 2, (((tensor_prod_end_nodes n d (fun i => B i (y i))).kronecker F0 * ρ).trace).re.
-/

/-- The closed network correlator I for n tripartite sources. -/
noncomputable def closed_network_correlator_I (n d m : ℕ)
    (B : Fin n → Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (F0 : Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix ((Fin n → Fin d) × Fin m) ((Fin n → Fin d) × Fin m) ℂ) : ℝ := (1 / 2 : ℝ) ^ n * ∑ y : Fin n → Fin 2,
    (((tensor_prod_end_nodes n d (fun i => B i (y i))).kronecker F0 * ρ).trace).re
