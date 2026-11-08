import AFTD.Prelude

/-!
# BIBD

Topic: graphs   Node: 028fcb39db10

Provenance: formalization of a published result. Source: arXiv:2611.05762 Def 6.2.1

A structure BIBD parameterized by types X and B and natural numbers v, b, r, k, lam, with fields: card_points asserting Nat.card X = v; card_blocks asserting Nat.card B = b; incomplete asserting k < v; block_pts assigning to each block b_idx : B an indexed map Fin k → X; block_inj asserting that block_pts b_idx is injective for each b_idx : B; replication asserting that for every point x : X, the Nat.card of the subtype of blocks b_idx : B containing x (satisfying ∃ j : Fin k, block_pts b_idx j = x) equals r; and balance asserting that for every pair of distinct points x, y : X, the Nat.card of the subtype of blocks b_idx : B containing both x and y equals lam.
-/

/-- A balanced incomplete block design (BIBD) with parameters (v, b, r, k, λ). -/
structure BIBD (X B : Type*) (v b r k lam : ℕ) where
  card_points : Nat.card X = v
  card_blocks : Nat.card B = b
  incomplete : k < v
  block_pts : B → Fin k → X
  block_inj : ∀ b_idx : B, Function.Injective (block_pts b_idx)
  replication : ∀ x : X, Nat.card {b_idx : B // ∃ j : Fin k, block_pts b_idx j = x} = r
  balance : ∀ ⦃x y : X⦄, x ≠ y →
    Nat.card {b_idx : B // (∃ j : Fin k, block_pts b_idx j = x) ∧
                           (∃ j' : Fin k, block_pts b_idx j' = y)} = lam
