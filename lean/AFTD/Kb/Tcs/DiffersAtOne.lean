import AFTD.Prelude

/-!
# differs_at_one

Topic: combinatorics   Node: c1a37467901d

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2.1

Two functions f and g of type ι → ℤˣ (taking values in the units of ℤ, {+1, -1}) differ at exactly one index if there is a unique index i : ι such that f i ≠ g i.
-/

/-- Two sign vectors f, g : ι → ℤˣ differ at exactly one index. -/
def differs_at_one {ι : Type*} (f g : ι → ℤˣ) : Prop :=
  ∃! i : ι, f i ≠ g i
