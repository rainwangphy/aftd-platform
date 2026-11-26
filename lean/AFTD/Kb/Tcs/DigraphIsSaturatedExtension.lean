import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsExtension
import AFTD.Kb.Tcs.DigraphExpansion
import AFTD.Kb.Tcs.DigraphClosedOutNbr

/-!
# digraph_is_saturated_extension

Topic: graphs   Node: 0cf459f731c1

Provenance: formalization of a published result. Source: scout/2611-32872-a-short-proof-of-seymour-s-second-neighborhood-conjecture.md:182

For a finite type V with decidable equality and directed graphs G and H on V with decidable adjacency relations, H is a saturated extension of G (digraph_is_saturated_extension G H) if H is an extension of G (digraph_is_extension G H) and for every extension H' of G with decidable adjacency relation such that H is a subgraph of H' (H ≤ H'), the total expansion of H with respect to G, given by the sum over all v : V of digraph_expansion G (digraph_closed_out_nbr H {v}), is at most the total expansion of H' with respect to G, given by the sum over all v : V of digraph_expansion G (digraph_closed_out_nbr H' {v}).
-/

/-- An extension H of G is saturated if no extension H' containing H has strictly smaller total expansion. -/
def digraph_is_saturated_extension {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop := digraph_is_extension G H ∧
  ∀ (H' : Digraph V) [DecidableRel H'.Adj],
    digraph_is_extension G H' → H ≤ H' →
      (∑ v : V, digraph_expansion G (digraph_closed_out_nbr H {v})) ≤
        (∑ v : V, digraph_expansion G (digraph_closed_out_nbr H' {v}))
