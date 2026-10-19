import AFTD.Prelude
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum

/-!
# davenport_constant_support

Topic: elementary_number_theory   Node: 9f058d513133

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 1 (the quantity D^{(d+1)}).

D^{(k)}(X): the maximal length (a supremum in ℕ∞) of a minimal zero-sum sequence over X whose support has exactly k elements.
-/

/-- `D^{(k)}(X)`: the supremum of the lengths of minimal zero-sum sequences over `X` whose support has exactly `k` elements. -/
noncomputable def davenport_constant_support {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (k : ℕ) (X : Set G) : ℕ∞ :=
  sSup {n | ∃ s : Multiset G, (∀ x ∈ s, x ∈ X) ∧ multiset_is_minimal_zero_sum s ∧
    s.toFinset.card = k ∧ (Multiset.card s : ℕ∞) = n}
