import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.OrderedTriple

/-!
# positive_fibre_three

Topic: combinatorics   Node: 5cdbba9771e1

Provenance: formalization of a published result. Source: arXiv:2610.03808 Prop. 6.8

The positive fibre of a function u : OrderedTriple α → ℤˣ on a linearly ordered type α is the function on OrderedTriple (WithTop α) with values in ℤˣ that equals u on triples in α and equals 1 on any triple containing ⊤.
-/

/-- The positive fibre embedding of a sign vector into a chirotope on WithTop α, setting all triples containing infinity to 1. -/
def positive_fibre_three {α : Type*} [LinearOrder α] (u : OrderedTriple α → ℤˣ) (t : OrderedTriple (WithTop α)) : ℤˣ :=
  match t with
  | ⟨some a, some b, some c, hab, hbc⟩ =>
    u ⟨a, b, c, WithTop.coe_lt_coe.mp hab, WithTop.coe_lt_coe.mp hbc⟩
  | _ => 1
