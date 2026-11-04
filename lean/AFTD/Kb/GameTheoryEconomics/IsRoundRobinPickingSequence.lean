import AFTD.Prelude

/-!
# is_round_robin_picking_sequence

Topic: fair_division   Node: eed1fe5c2003

Provenance: formalization of a published result. Source: arXiv:2611.00432, Section 3

A picking sequence σ : ℕ → Fin n is a round-robin sequence if there exists a permutation π of Fin n such that the agent picking at turn k is π(k mod n).
-/

/-- A round-robin picking sequence repeats a fixed permutation of the agents. -/
def is_round_robin_picking_sequence (n : ℕ) [NeZero n] (σ : ℕ → Fin n) : Prop := ∃ π : Equiv.Perm (Fin n), ∀ k : ℕ, σ k = π ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩
