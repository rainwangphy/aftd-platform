import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_lifting_config

Topic: combinatorics   Node: a28049537dc8

Provenance: helper lemma. step towards op_1370_no_private_sharp_all_dimensions

An inductive lifting configuration on Fin n consists of three families 𝒜 0, 𝒜 1, 𝒜 2 and two auxiliary families L0, L2 of subsets of Fin n satisfying the sharp no-private conditions, strong incomparability, uncomplementedness, total size 2^(n-1)-2, |𝒜 1| = 1, |L0| + |L2| = 2^(n-1), disjointness of complement orbits between L0, L2 and 𝒜, and mixed incomparability.
-/

/-- Inductive lifting configuration for OP-1370: three families 𝒜 and two auxiliary families L0, L2 satisfying no-private conditions, strong incomparability, uncomplementedness, exact cardinality 2^(n-1)-2, and cross-complement and mixed incomparability invariants. -/
def op1370_lifting_config (n : ℕ) : Prop := ∃ (𝒜 : Fin 3 → Finset (Finset (Fin n))) (L0 L2 : Finset (Finset (Fin n))),
    (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧
    (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧
    (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧
    (∑ i, (𝒜 i).card) = 2 ^ (n - 1) - 2 ∧
    (𝒜 1).card = 1 ∧ L0.Nonempty ∧ L2.Nonempty ∧
    is_uncomplemented L0 ∧ is_uncomplemented L2 ∧
    L0.card + L2.card = 2 ^ (n - 1) ∧
    (∀ A ∈ L0, ∀ B ∈ L2, ¬ A ⊆ B ∧ ¬ B ⊆ A) ∧
    (∀ S ∈ L0, Sᶜ ∉ 𝒜 0) ∧ (∀ S ∈ L2, Sᶜ ∉ 𝒜 2) ∧
    (∀ A ∈ L0, ∀ B ∈ 𝒜 1, ¬ A ⊆ B) ∧ (∀ A ∈ L0, ∀ B ∈ 𝒜 2, ¬ A ⊆ B) ∧
    (∀ A ∈ L2, ∀ B ∈ 𝒜 0, ¬ A ⊆ B) ∧ (∀ A ∈ L2, ∀ B ∈ 𝒜 1, ¬ A ⊆ B)
