import AFTD.Prelude

/-!
# poset_tower

Topic: combinatorics   Node: f2c0d4b3d903

Provenance: original. Related work: arXiv:2610.20802 Sec. 5

Given an unbundled type α equipped with a partial order [PartialOrder α], the function poset_tower (α : Type*) [PartialOrder α] : ℕ → PartOrd is defined by pattern matching on ℕ: poset_tower α 0 = PartOrd.of α, poset_tower α 1 = PartOrd.of α, and for k + 1, poset_tower α (k + 1) = PartOrd.of (poset_tower α k →o α), the bundled partial order PartOrd of order-preserving maps from poset_tower α k to α ordered pointwise.
-/

/-- The sequence of partially ordered sets formed by right-associated iterated exponentiation, where T 0 X = X, T 1 X = X, and T (k + 1) X = X^(T k X). -/
def poset_tower (α : Type*) [PartialOrder α] : ℕ → PartOrd
| 0 => PartOrd.of α
| 1 => PartOrd.of α
| k + 1 => PartOrd.of (poset_tower α k →o α)
