import AFTD.Prelude

/-!
# booleanDegree

Topic: combinatorics   Node: 4058cdc12746

Provenance: formalization of a published result. Source: arXiv:2611.03452, Section 2.4

The degree of a Boolean function p : (Fin n → ZMod 2) → ZMod 2 is the maximum cardinality of a subset S of coordinates such that the algebraic normal form coefficient c_S is nonzero.
-/

open scoped BigOperators in
/-- The F_2-degree of a Boolean function p : (Fin n → ZMod 2) → ZMod 2, defined as the maximum size of a monomial with nonzero coefficient in its algebraic normal form. -/
noncomputable def booleanDegree {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) : ℕ := Finset.sup (Finset.univ.filter (fun S : Finset (Fin n) =>
    (∑ x ∈ Finset.univ.filter (fun (x : Fin n → ZMod 2) => ∀ i, x i ≠ 0 → i ∈ S), p x) ≠ 0)) Finset.card
