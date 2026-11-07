import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedRamseyProp

/-!
# ordered_ramsey_number

Topic: graphs   Node: 6d6814317f40

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

The ordered Ramsey number R_ord(H, H') of ordered graphs H and H' is the infimum of natural numbers N such that every 2-edge-colouring of the complete ordered graph on N vertices contains an ordered copy of H in the first colour or H' in the second colour.
-/

/-- The ordered Ramsey number R_ord(H, H') is the minimum N such that every 2-edge-colouring of K_N ordered contains H in the first colour or H' in the second colour. -/
noncomputable def ordered_ramsey_number {α β : Type*} [LinearOrder α] [LinearOrder β]
    (H : SimpleGraph α) (H' : SimpleGraph β) : ℕ := sInf {N : ℕ | ordered_ramsey_prop H H' N}
