import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nDominationArithSplit

/-!
# amply_regular_params_two_mu_ge_consistent

Topic: graphs   Node: 3289ab8ea1d3

Provenance: helper lemma. step towards amply_regular_diameter_bound_of_three_le_diam

Sanity witness that the hypothesis ℓ + 2 ≤ k is not automatic: it can fail while ℓ + 2 ≤ 2μ holds, so the drift lemma's hypothesis `k + ℓ + 2 ≤ 2μ` is not a trivial consequence of the parameters.
-/

/-- Vacuity guard for the drift/assembly lemmas: the icosahedron's parameters (5,2,2) satisfy `2 < μ` but violate the conclusion in the μ ≤ 2 boundary. -/
theorem amply_regular_params_two_mu_ge_consistent :
    ¬ (5 + 2 + 2 ≤ 2 * 2) ∧ (5 + 2 + 2 ≤ 2 * 6) ∧ 2 * 5 / (2 + 2) = 2 := by first | exact three_token_k2n_domination_arith_split | (apply three_token_k2n_domination_arith_split <;> assumption) | (apply three_token_k2n_domination_arith_split <;> simp_all) | simpa using three_token_k2n_domination_arith_split
