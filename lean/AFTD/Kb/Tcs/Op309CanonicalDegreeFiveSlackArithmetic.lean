import AFTD.Prelude

/-!
# op309_canonical_degree_five_slack_arithmetic

Topic: graphs   Node: 3ab71fd70c4d

Provenance: helper lemma. OP-309 conditional clean-component counting route; experiment 42127. The graph-level p≤18b+s premise is not proved.

If nonnegative integer counts of paths, stars, covered-to-covered links, uncovered vertices, and total vertices satisfy the two stated component and boundary identities and p≤18b+s, then 125u≤44n.
-/

theorem op309_canonical_degree_five_slack_arithmetic
    (p s b u n : ℕ)
    (hn : n = 3*p + 4*s + u)
    (hboundary : 3*u + 2*b = 5*p + 6*s)
    (hclean : p ≤ 18*b + s) : 125*u ≤ 44*n := by
  omega
