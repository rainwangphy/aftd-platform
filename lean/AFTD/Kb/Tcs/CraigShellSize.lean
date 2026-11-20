import AFTD.Prelude

/-!
# craig_shell_size

Topic: information   Node: c4ef593e21e3

Provenance: formalization of a published result. Source: arXiv:2611.22441 Definition 2, Lemma 6, Corollary 1

For natural numbers p and k, craig_shell_size p k is the number of pairs of disjoint k-element subsets of Fin p whose elements have identical power sums in ZMod p for all exponents 1 ≤ r < k, representing the size of the shortest vector shell of Euclidean norm √(2k) in Craig's lattice A_{p-1}^k.
-/

/-- The number of shortest nonzero vectors (norm √(2k)) in Craig's lattice A_{p-1}^k. -/
def craig_shell_size (p k : ℕ) : ℕ :=
  ((Finset.powerset Finset.univ ×ˢ Finset.powerset Finset.univ).filter fun (⟨S1, S2⟩ : Finset (Fin p) × Finset (Fin p)) =>
    S1.card = k ∧ S2.card = k ∧ Disjoint S1 S2 ∧
      ∀ r : ℕ, 1 ≤ r → r < k → (∑ x ∈ S1, (x.val : ZMod p) ^ r = ∑ x ∈ S2, (x.val : ZMod p) ^ r)).card
