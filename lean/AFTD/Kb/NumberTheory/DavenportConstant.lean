import AFTD.Prelude
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum

/-!
# davenport_constant

Topic: elementary_number_theory   Node: 47c64a930a50

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 1 (Davenport constant of a subset; taken in ℕ∞ so that no finiteness argument is needed to state it).

The Davenport constant D(X) of a subset X of an abelian group: the supremum (in ℕ ∪ {∞}) of the lengths of minimal zero-sum sequences with all terms in X.
-/

/-- The Davenport constant `D(X)`, as a supremum in `ℕ∞`. -/
noncomputable def davenport_constant {G : Type*} [AddCommMonoid G] (X : Set G) : ℕ∞ :=
  sSup {n | ∃ s : Multiset G, (∀ x ∈ s, x ∈ X) ∧ multiset_is_minimal_zero_sum s ∧
    (Multiset.card s : ℕ∞) = n}
