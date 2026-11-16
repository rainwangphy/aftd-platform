import AFTD.Prelude
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing

/-!
# is_joint_error_correcting_detecting

Topic: information   Node: 03c16fde4ba5

Provenance: formalization of a published result. Source: arXiv:2611.18156 Definition II.4, Theorem III.3

Given implicit parameters n and q, a code C : Finset (Fin n → Fin q) is a (c, c') joint error-correcting and detecting code if distinct codewords in C have disjoint radius-c Hamming balls, and every codeword's radius-c Hamming ball is disjoint from every codeword's (c, c') Hamming ring.
-/

/-- Predicate for a code C in (Fin n → Fin q) to be (c, c') joint error-correcting and detecting. -/
def is_joint_error_correcting_detecting {n q : ℕ} (c c' : ℕ) (C : Finset (Fin n → Fin q)) : Prop :=
  (∀ x₁ ∈ C, ∀ x₂ ∈ C, x₁ ≠ x₂ → Disjoint (hamming_ball c x₁) (hamming_ball c x₂)) ∧
  (∀ x₁ ∈ C, ∀ x₂ ∈ C, Disjoint (hamming_ball c x₁) (hamming_ring c c' x₂))
