import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformIsRandAlg
import AFTD.Kb.Tcs.GenKServerUniformExpectedCost
import AFTD.Kb.Tcs.GenKServerUniformOpt

/-!
# gen_k_server_uniform_competitive

Topic: online_algorithms   Node: fe1ed5f32900

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2: a randomized online algorithm is γ-competitive against an oblivious adversary if E[ALG(ρ)] ≤ γ·OPT(ρ) + c for every finite request sequence ρ, with c allowed to depend on the start configuration a

Generalized k-server on k uniform metrics with m points each: configurations and requests are functions Fin k → Fin m. With k m : ℕ implicit, the predicate takes, in this order, P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ, a start configuration a : Fin k → Fin m and a real γ, and holds when gen_k_server_uniform_is_rand_alg P and there is a real constant c such that for every ρ : List (Fin k → Fin m), gen_k_server_uniform_expected_cost P a ρ ≤ γ * (gen_k_server_uniform_opt a ρ : ℝ) + c.
-/

/-- `P` is a γ-competitive randomized online algorithm (oblivious adversary) for generalized k-server on uniform metrics `Fin m`, started in `a`. -/
def gen_k_server_uniform_competitive {k m : ℕ}
    (P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ)
    (a : Fin k → Fin m) (γ : ℝ) : Prop :=
  gen_k_server_uniform_is_rand_alg P ∧
    ∃ c : ℝ, ∀ ρ : List (Fin k → Fin m),
      gen_k_server_uniform_expected_cost P a ρ ≤ γ * (gen_k_server_uniform_opt a ρ : ℝ) + c
