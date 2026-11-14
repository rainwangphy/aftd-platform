import AFTD.Prelude

/-!
# graph_125_exceptional_coloring_arithmetic

Topic: graphs   Node: 3d6749350d0b

Provenance: helper lemma. Exceptional-vertex arithmetic for OP-110; experiment 26134.

The displayed overlap, degree, indegree and color-class budget inequalities imply a total crossing budget of at most fifty.
-/

theorem graph_125_exceptional_coloring_arithmetic (z d t a : ℕ)
    (hzlo : 42 ≤ z) (hzhi : z ≤ 43) (hd : 46 ≤ d)
    (ht : 6 * t ≤ d + z) (hcap : d + z ≤ 124)
    (ha : t + 7 ≤ 3 * a) :
    (124 - z - d) + (t + 7 - a) ≤ 50 := by
  omega
