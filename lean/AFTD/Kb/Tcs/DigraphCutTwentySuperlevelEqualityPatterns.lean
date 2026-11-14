import AFTD.Prelude

/-!
# digraph_cut_twenty_superlevel_equality_patterns

Topic: graphs   Node: f55d5e574aeb

Provenance: helper lemma. Finite arithmetic in experiment 26240; equality case of digraph_seven_out_robust_cut_thresholds.

The five robust two-cycle superlevel alternatives have exactly four equality patterns when their six counts sum to twenty.
-/

theorem digraph_cut_twenty_superlevel_equality_patterns
    (n1 n2 n3 n4 n5 n6 : ℕ)
    (hmono : n6 ≤ n5 ∧ n5 ≤ n4 ∧ n4 ≤ n3 ∧ n3 ≤ n2 ∧ n2 ≤ n1)
    (hsum : n1+n2+n3+n4+n5+n6=20)
    (h6 : 1 ≤ n6 ∨ 3 ≤ n5) (h5 : 2 ≤ n5 ∨ 4 ≤ n4)
    (h4 : 3 ≤ n4 ∨ 5 ≤ n3) (h3 : 4 ≤ n3 ∨ 6 ≤ n2)
    (h2 : 5 ≤ n2 ∨ 7 ≤ n1) :
    (n1=5 ∧ n2=5 ∧ n3=4 ∧ n4=3 ∧ n5=3 ∧ n6=0) ∨
    (n1=5 ∧ n2=5 ∧ n3=4 ∧ n4=4 ∧ n5=1 ∧ n6=1) ∨
    (n1=5 ∧ n2=5 ∧ n3=5 ∧ n4=2 ∧ n5=2 ∧ n6=1) ∨
    (n1=5 ∧ n2=5 ∧ n3=4 ∧ n4=3 ∧ n5=2 ∧ n6=1) := by
  rcases h6 with h6 | h6 <;> rcases h5 with h5 | h5 <;> rcases h4 with h4 | h4 <;>
    rcases h3 with h3 | h3 <;> rcases h2 with h2 | h2 <;> omega
