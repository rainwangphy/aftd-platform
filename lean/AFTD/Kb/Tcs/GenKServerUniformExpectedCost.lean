import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformExpectedCostFrom

/-!
# gen_k_server_uniform_expected_cost

Topic: online_algorithms   Node: 9e2f107b2b7d

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2: E[ALG(ρ)] for an algorithm starting in configuration a

Generalized k-server on k uniform metrics with m points each: configurations and requests are functions Fin k → Fin m. With k m : ℕ implicit, the function takes, in this order, transition probabilities P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ, a start configuration a : Fin k → Fin m and a request list ρ : List (Fin k → Fin m), and returns the real number gen_k_server_uniform_expected_cost_from P [] (fun x => if x = a then 1 else 0) ρ: the expected cost of P on ρ started from the point mass at a, with no earlier requests.
-/

/-- Expected cost E[ALG(ρ)] of the randomized online algorithm `P` started in configuration `a`. -/
noncomputable def gen_k_server_uniform_expected_cost {k m : ℕ}
    (P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ)
    (a : Fin k → Fin m) (ρ : List (Fin k → Fin m)) : ℝ :=
  gen_k_server_uniform_expected_cost_from P [] (fun x => if x = a then 1 else 0) ρ
