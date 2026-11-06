import AFTD.Prelude
import AFTD.Kb.Tcs.Hn

/-!
# hypergraphState

Topic: quantum   Node: fb1feda318db

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For a natural number n and a hypergraph H : Finset (Finset (Fin n)), hypergraphState n H is the quantum state vector in Hn n whose amplitude at each bitstring x : Fin n → Fin 2 is (1 / Real.sqrt (2 ^ n)) * ∏ e ∈ H, (if ∀ i ∈ e, x i = 1 then -1 else 1).
-/

/-- The quantum hypergraph state in Hn n associated to a hypergraph H. -/
noncomputable def hypergraphState (n : ℕ) (H : Finset (Finset (Fin n))) : Hn n := EuclideanSpace.equiv (Fin n → Fin 2) ℂ |>.symm (fun x => (1 / Real.sqrt (2 ^ n : ℝ) : ℂ) * ∏ e ∈ H, if ∀ i ∈ e, x i = 1 then (-1 : ℂ) else 1)
