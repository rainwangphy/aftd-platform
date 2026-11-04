import AFTD.Prelude
import AFTD.Kb.Tcs.IsRankOneProduct
import AFTD.Kb.Tcs.CnfLit

/-!
# has_depth_three_amc_proof

Topic: proof_complexity   Node: 9ddd5caa9fc8

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.3, formula (2)

Let n be a natural number, A a DNF formula represented as a list of terms where each term is a list of literals of type CnfLit (Fin n), ε a real shift parameter, and r a natural number. Then has_depth_three_amc_proof n A ε r holds if and only if there exists a family of r functions R : Fin r → (Fin n → Bool) → ℝ such that every R j is a nonnegative rank-one product (is_rank_one_product (R j)), and for every truth assignment τ : Fin n → Bool, the number of terms in A satisfied by τ (counted as the length of the sublist of terms in A whose literals all evaluate to true under τ) minus ε equals the sum over j : Fin r of R j τ.
-/

open scoped Classical BigOperators in
/-- A DNF formula has a depth-three AMC proof of size r at shift parameter ε if its satisfied-term count minus ε is a sum of r nonnegative rank-one product functions. -/
def has_depth_three_amc_proof (n : ℕ) (A : List (List (CnfLit (Fin n)))) (ε : ℝ) (r : ℕ) : Prop := ∃ R : Fin r → (Fin n → Bool) → ℝ,
    (∀ j, is_rank_one_product (R j)) ∧
    ∀ τ : Fin n → Bool,
      ((A.filter (fun t => ∀ l ∈ t, match l with
        | CnfLit.pos v => τ v = true
        | CnfLit.neg v => τ v = false)).length : ℝ) - ε = ∑ j : Fin r, R j τ
