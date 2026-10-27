import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# is_rank_three_signotope

Topic: combinatorics   Node: 04c6f4fd0ca3

Provenance: formalization of a published result. Source: arXiv:2610.03808 Def. 2.1, Def. 6.7

A function u : OrderedTriple α → ℤˣ assigning units of ℤ ({+1, -1}) to ordered triples in a linearly ordered type α is a rank-3 signotope if for all a < b < c < d in α, the sequence of four values (u(abc), u(abd), u(acd), u(bcd)) has at most one sign change (no alternating pattern of length 3).
-/

/-- A map from ordered triples to signs ℤˣ is a rank-3 signotope if every 4-element packet has at most one sign change. -/
def is_rank_three_signotope {α : Type*} [LinearOrder α] (u : OrderedTriple α → ℤˣ) : Prop :=
  ∀ (a b c d : α) (hab : a < b) (hbc : b < c) (hcd : c < d),
    let x₁ := u ⟨a, b, c, hab, hbc⟩
    let x₂ := u ⟨a, b, d, hab, hbc.trans hcd⟩
    let x₃ := u ⟨a, c, d, hab.trans hbc, hcd⟩
    let x₄ := u ⟨b, c, d, hbc, hcd⟩
    ¬ (x₁ = x₃ ∧ x₁ ≠ x₂) ∧ ¬ (x₁ = x₄ ∧ x₁ ≠ x₂) ∧ ¬ (x₁ = x₄ ∧ x₁ ≠ x₃) ∧ ¬ (x₂ = x₄ ∧ x₂ ≠ x₃)
