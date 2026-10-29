import AFTD.Prelude
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraph
import AFTD.Kb.Tcs.SimpleGraphHasEdgeDisjointPerfectMatchings
import AFTD.Kb.Tcs.Op652HalfDegreePackingOfMinDegreeLeTwo
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraphDecidableAdj

/-!
# op_657_half_degree_packing_of_min_degree_le_two

Topic: graphs   Node: 98e30f65fc9d

Provenance: helper lemma. arXiv:2610.37512, Coprime matchings of divisor sets

For every squarefree natural number n with at least two distinct prime factors and any positive coprime integers a and b, if the coprime divisor progression graph B has minimum degree at most 2 and contains a perfect matching, then B contains at least ⌈δ(B)/2⌉ pairwise edge-disjoint perfect matchings.
-/

/-- If the coprime divisor progression graph for squarefree n has minimum degree at most 2 and has a perfect matching, it has at least ⌈δ/2⌉ edge-disjoint perfect matchings. -/
theorem op_657_half_degree_packing_of_min_degree_le_two
    (n : ℕ) (hn : Squarefree n) (hprimes : 2 ≤ n.primeFactors.card)
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (hdeg : (coprime_divisor_progression_graph n a b).minDegree ≤ 2)
    (hM : ∃ M : (coprime_divisor_progression_graph n a b).Subgraph, M.IsPerfectMatching) :
    simple_graph_has_edge_disjoint_perfect_matchings
      (coprime_divisor_progression_graph n a b)
      (((coprime_divisor_progression_graph n a b).minDegree + 1) / 2) := by
  have hn2 : 2 ≤ n := by
    by_contra! hlt
    interval_cases n <;> simp at hprimes
  exact op_652_half_degree_packing_of_min_degree_le_two n hn2 a b hb hdeg hM
