import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# has_depth_three_amc_bounded_bias_proof

Topic: proof_complexity   Node: 54fe87660367

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.3, Definition 2.5 and formula (1)

Let n be a natural number, A a DNF formula represented as a list of terms where each term is a list of literals of type CnfLit (Fin n), ε a real shift parameter, and s a natural number. Then has_depth_three_amc_bounded_bias_proof n A ε s holds if and only if there exists a family of s functions R : Fin s → (Fin n → Bool) → ℝ such that for every j : Fin s, R j is a bounded-bias rank-one product—meaning there exists g : Fin n → Bool → ℝ with 0 ≤ g i b for all i and b, and for each i, g i true = 0, g i false = 0, or g i true = g i false, such that R j τ = ∏ i : Fin n, g i (τ i)—and for every truth assignment τ : Fin n → Bool, the number of terms in A satisfied by τ (the length of the sublist of terms in A whose literals all evaluate to true under τ) minus ε equals the sum over j : Fin s of R j τ.
-/

open scoped Classical BigOperators in
/-- A DNF formula has a bounded-bias depth-three AMC proof of size s at shift parameter ε if its satisfied-term count minus ε is a sum of s bounded-bias rank-one products. -/
def has_depth_three_amc_bounded_bias_proof (n : ℕ) (A : List (List (CnfLit (Fin n)))) (ε : ℝ) (s : ℕ) : Prop := ∃ R : Fin s → (Fin n → Bool) → ℝ,
    (∀ j, ∃ g : Fin n → Bool → ℝ,
      (∀ i b, 0 ≤ g i b) ∧
      (∀ i, g i true = 0 ∨ g i false = 0 ∨ g i true = g i false) ∧
      ∀ τ, R j τ = ∏ i : Fin n, g i (τ i)) ∧
    ∀ τ : Fin n → Bool,
      ((A.filter (fun t => ∀ l ∈ t, match l with
        | CnfLit.pos v => τ v = true
        | CnfLit.neg v => τ v = false)).length : ℝ) - ε = ∑ j : Fin s, R j τ
