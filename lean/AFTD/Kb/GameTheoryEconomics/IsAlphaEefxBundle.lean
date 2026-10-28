import AFTD.Prelude

/-!
# is_alpha_eefx_bundle

Topic: fair_division   Node: 6c9c16b907a7

Provenance: formalization of a published result. Source: arXiv:2610.34625 Def. 2.1

A bundle S of goods is alpha-EEFX for an agent with valuation v if there exists a partition of the remaining goods into n-1 parts such that the agent's value for S is at least alpha times her value for any part after removing any item from it.
-/

/-- A bundle S is alpha-EEFX for an agent if there is an (n-1)-partition of G \ S such that v(S) >= alpha * v(Y_p \ {g}) for all parts and items. -/
def is_alpha_eefx_bundle {m : ℕ} (v : Finset (Fin m) → ℝ) (n : ℕ) (α : ℝ) (S : Finset (Fin m)) : Prop :=
  ∃ Y : Fin (n - 1) → Finset (Fin m),
    (∀ p q : Fin (n - 1), p ≠ q → Disjoint (Y p) (Y q)) ∧
    (Finset.biUnion Finset.univ Y = Finset.univ \ S) ∧
    ∀ p : Fin (n - 1), ∀ g ∈ Y p, α * v ((Y p).erase g) ≤ v S
