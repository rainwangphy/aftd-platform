import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset

/-!
# inst_partial_order_diamond_poset

Topic: combinatorics   Node: d62af8453214

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k

The partial order on DiamondPoset j where bot is less than or equal to every element, every element is less than or equal to top, and two middle elements mid a and mid b are comparable if and only if a = b.
-/

/-- Partial order on DiamondPoset j where bot is minimum, top is maximum, and middle elements are pairwise incomparable. -/
instance inst_partial_order_diamond_poset (j : ℕ) : PartialOrder (DiamondPoset j) where
  le x y := match x, y with
    | .bot, _ => True
    | _, .top => True
    | .mid a, .mid b => a = b
    | _, _ => False
  le_refl := by
    rintro (_ | _ | _) <;> trivial
  le_trans := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
      aesop
  le_antisymm := by
    rintro (_ | _ | _) (_ | _ | _) <;>
      aesop
