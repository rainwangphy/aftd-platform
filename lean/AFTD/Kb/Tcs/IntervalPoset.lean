import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# IntervalPoset

Topic: combinatorics   Node: cd990eba485a

Provenance: formalization of a published result. Source: arXiv:1311.3922 Def. 2.7

An interval-poset is a strict partial order on a linearly ordered set satisfying the Tamari convexity conditions: if a < b < c and a ≺ c then b ≺ c, and if a < b < c and c ≺ a then b ≺ a.
-/

/-- An interval-poset on a linearly ordered type α is a strict partial order satisfying Tamari convexity. -/
structure IntervalPoset (α : Type*) [LinearOrder α] where
  rel : α → α → Prop
  irrefl : ∀ x, ¬ rel x x
  trans : ∀ x y z, rel x y → rel y z → rel x z
  convex_inc : ∀ a b c : α, a < b → b < c → rel a c → rel b c
  convex_dec : ∀ a b c : α, a < b → b < c → rel c a → rel b a
