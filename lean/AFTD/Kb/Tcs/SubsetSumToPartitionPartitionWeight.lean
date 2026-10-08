import AFTD.Prelude

/-!
# SubsetSumToPartition.partitionWeight

Topic: np_completeness   Node: d2f0341c0e93

Provenance: formalization of a published result. Source: TCSlib, `SubsetSumToPartition.partitionWeight`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean (Apache-2.0); 1 verbatim; compiled here.

The weight function on the augmented universe $U \oplus \mathrm{Bool}$ built from a Subset
Sum instance $(w, T)$. Writing $W = \sum_{a} w(a)$, it sends the original item
$\mathrm{inl}\,a$ to $w(a)$, the first dummy item $\mathrm{inr}\,\mathsf{true}$ to
$2W - T$, and the second dummy item $\mathrm{inr}\,\mathsf{false}$ to $W + T$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {U : Type*} [Fintype U] [DecidableEq U] in
/-- Reduction from Subset Sum to Partition. We create a new type `B` by taking the disjoint union of `U` and `Bool`. `U ⊕ Bool` acts as our new set, adding exactly two new "dummy" items: - `Sum.inl a` represents the original elements from `A`. - `Sum.inr true` represents our first dummy item 'y'. - `Sum.inr false` represents our second dummy item 'z'. -/
def SubsetSumToPartition.partitionWeight (w : U → ℕ) (T : ℕ) : U ⊕ Bool → ℕ
  | Sum.inl a => w a
  | Sum.inr true => 2 * (∑ a, w a) - T
  | Sum.inr false => (∑ a, w a) + T
