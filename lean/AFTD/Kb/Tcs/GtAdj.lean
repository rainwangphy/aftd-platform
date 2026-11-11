import AFTD.Prelude
import AFTD.Kb.Tcs.GtVertex

/-!
# gt_adj

Topic: graphs   Node: a8c36a5eef4d

Provenance: formalization of a published result. Source: arXiv:2611.11352 Definition 1, Definition 2

The adjacency relation gt_adj t on GtVertex t: vertices u and v are adjacent if and only if (u is in A and v is in B, or vice versa), (u is in B and v is in C, or vice versa), (u is in C and v is in D, or vice versa), (one is in {A, B, C, D} and the other in {P, Q, R}), (u is in P and v is in Q, or vice versa), (u is in P and v is in R, or vice versa), (u is in Q and v is in R, or vice versa), or both are distinct vertices R i and R j with i ≠ j.
-/

/-- Adjacency relation of G_t. -/
def gt_adj (t : ℕ) : GtVertex t → GtVertex t → Prop := fun u v => match u, v with
  | .A _, .B _ => True
  | .B _, .A _ => True
  | .B _, .C _ => True
  | .C _, .B _ => True
  | .C _, .D _ => True
  | .D _, .C _ => True
  | .A _, .P _ => True | .P _, .A _ => True
  | .A _, .Q _ => True | .Q _, .A _ => True
  | .A _, .R _ => True | .R _, .A _ => True
  | .B _, .P _ => True | .P _, .B _ => True
  | .B _, .Q _ => True | .Q _, .B _ => True
  | .B _, .R _ => True | .R _, .B _ => True
  | .C _, .P _ => True | .P _, .C _ => True
  | .C _, .Q _ => True | .Q _, .C _ => True
  | .C _, .R _ => True | .R _, .C _ => True
  | .D _, .P _ => True | .P _, .D _ => True
  | .D _, .Q _ => True | .Q _, .D _ => True
  | .D _, .R _ => True | .R _, .D _ => True
  | .P _, .Q _ => True | .Q _, .P _ => True
  | .P _, .R _ => True | .R _, .P _ => True
  | .Q _, .R _ => True | .R _, .Q _ => True
  | .R i, .R j => i ≠ j
  | _, _ => False
