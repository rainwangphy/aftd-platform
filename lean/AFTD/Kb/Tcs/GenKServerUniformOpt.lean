import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformPathCost

/-!
# gen_k_server_uniform_opt

Topic: online_algorithms   Node: 1eb604b11138

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2: OPT(ρ), the minimum cost of an offline solution starting from a

For a start configuration a : Fin k → Fin m and a request list ρ, OPT is the infimum (sInf in ℕ) of the natural numbers c such that some list os of configurations satisfies List.Forall₂ (fun o r => ∃ i, o i = r i) os ρ (os has the same length as ρ and its t-th configuration serves the t-th request) and gen_k_server_uniform_path_cost a os = c.
-/

/-- Offline optimum OPT(ρ): the least movement cost of a sequence of configurations, started from `a`, whose t-th configuration serves the t-th request. -/
noncomputable def gen_k_server_uniform_opt {k m : ℕ} (a : Fin k → Fin m) (ρ : List (Fin k → Fin m)) : ℕ :=
  sInf {c | ∃ os : List (Fin k → Fin m),
    List.Forall₂ (fun o r => ∃ i, o i = r i) os ρ ∧ gen_k_server_uniform_path_cost a os = c}
