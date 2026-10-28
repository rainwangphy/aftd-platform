import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformIsRandAlg

/-!
# gen_k_server_uniform_expected_cost_from

Topic: online_algorithms   Node: f2dcfb7fac42

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2: E[ALG(ρ)], the expected movement cost of a randomized online algorithm; auxiliary recursion over the remaining requests

Generalized k-server on k uniform metrics with m points each: both configurations and requests are functions Fin k → Fin m (one point per server). With k m : ℕ implicit, the function takes, in this order, transition probabilities P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ, a list past : List (Fin k → Fin m) of requests already served, a function μ : (Fin k → Fin m) → ℝ (the distribution of the current configuration), and a list rs : List (Fin k → Fin m) of remaining requests, and returns a real number, defined by recursion on rs: 0 for the empty list; for r :: rs it is (∑ over x, ∑ over y in Fin k → Fin m, of μ x * P past r x y * (hammingDist x y : ℝ)) plus the value of the function itself at past ++ [r], the new distribution (fun y => ∑ over x of μ x * P past r x y), and rs.
-/

/-- Expected movement cost (unit distances, Hamming distance between configurations) of serving the remaining requests, given the earlier requests and the current distribution of the configuration. -/
noncomputable def gen_k_server_uniform_expected_cost_from {k m : ℕ}
    (P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ) :
    List (Fin k → Fin m) → ((Fin k → Fin m) → ℝ) → List (Fin k → Fin m) → ℝ
  | _, _, [] => 0
  | past, μ, r :: rs =>
      (∑ x, ∑ y, μ x * P past r x y * (hammingDist x y : ℝ)) +
        gen_k_server_uniform_expected_cost_from P (past ++ [r]) (fun y => ∑ x, μ x * P past r x y) rs
