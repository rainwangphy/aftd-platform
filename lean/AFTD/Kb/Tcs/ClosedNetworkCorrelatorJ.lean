import AFTD.Prelude
import AFTD.Kb.Tcs.TensorProdEndNodes

/-!
# closed_network_correlator_J

Topic: quantum   Node: dc991c115f13

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 8

Given n, d, m : ℕ, end-node observables B : Fin n → Fin 2 → Matrix (Fin d) (Fin d) ℂ, central observable F1 : Matrix (Fin m) (Fin m) ℂ, and state ρ : Matrix ((Fin n → Fin d) × Fin m) ((Fin n → Fin d) × Fin m) ℂ, closed_network_correlator_J n d m B F1 ρ is (1 / 2 : ℝ) ^ n * ∑ y : Fin n → Fin 2, ((-1 : ℝ) ^ (∑ i : Fin n, (y i).val)) * (((tensor_prod_end_nodes n d (fun i => B i (y i))).kronecker F1 * ρ).trace).re.
-/

/-- The closed network correlator J with parity signs for n tripartite sources. -/
noncomputable def closed_network_correlator_J (n d m : ℕ)
    (B : Fin n → Fin 2 → Matrix (Fin d) (Fin d) ℂ)
    (F1 : Matrix (Fin m) (Fin m) ℂ)
    (ρ : Matrix ((Fin n → Fin d) × Fin m) ((Fin n → Fin d) × Fin m) ℂ) : ℝ := (1 / 2 : ℝ) ^ n * ∑ y : Fin n → Fin 2,
    ((-1 : ℝ) ^ (∑ i : Fin n, (y i).val)) *
      (((tensor_prod_end_nodes n d (fun i => B i (y i))).kronecker F1 * ρ).trace).re
