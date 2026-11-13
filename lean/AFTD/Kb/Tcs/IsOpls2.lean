import AFTD.Prelude
import AFTD.Kb.Tcs.IsPls

/-!
# is_opls2

Topic: combinatorics   Node: d21343795fa7

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 1

A pair of mutually orthogonal partial Latin squares of order n (2-OPLS(n)) is an n × n array of pairs such that both coordinate projections are partial Latin squares of order n and each ordered pair of symbols appears at most once in the array.
-/

/-- Predicate for a pair of mutually orthogonal partial Latin squares of order n. -/
def is_opls2 {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) : Prop :=
  is_pls (fun r c => (M r c).map Prod.fst) ∧
  is_pls (fun r c => (M r c).map Prod.snd) ∧
  (∀ (r₁ c₁ r₂ c₂ : Fin n) (p : Fin n × Fin n), M r₁ c₁ = some p → M r₂ c₂ = some p → r₁ = r₂ ∧ c₁ = c₂)
