import AFTD.Prelude
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraph
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraphDecidableAdj
import AFTD.Kb.Tcs.SimpleGraphHasEdgeDisjointPerfectMatchings

/-!
# op_652_half_degree_packing_of_min_degree_le_two

Topic: graphs   Node: f1e99dfe8a56

Provenance: helper lemma. arXiv:2610.37512

For any natural number n ≥ 2 and integers a, b with b > 0, if the coprime divisor progression graph B has minimum degree at most 2 and contains a perfect matching, then B contains at least ⌈δ(B)/2⌉ pairwise edge-disjoint perfect matchings.
-/

/-- OP-652 holds when the minimum degree of B is at most 2, since ceil(delta/2) <= 1. -/
theorem op_652_half_degree_packing_of_min_degree_le_two (n : ℕ) (hn : 2 ≤ n) (a b : ℤ) (hb : 0 < b)
    (hdeg : (coprime_divisor_progression_graph n a b).minDegree ≤ 2)
    (hM : ∃ M : (coprime_divisor_progression_graph n a b).Subgraph, M.IsPerfectMatching) :
    simple_graph_has_edge_disjoint_perfect_matchings
      (coprime_divisor_progression_graph n a b)
      (((coprime_divisor_progression_graph n a b).minDegree + 1) / 2) := by
  have hd : ((coprime_divisor_progression_graph n a b).minDegree + 1) / 2 = 0 ∨
            ((coprime_divisor_progression_graph n a b).minDegree + 1) / 2 = 1 := by omega
  rcases hd with h0 | h1
  · rw [h0]
    use fun i => Fin.elim0 i
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · rw [h1]
    obtain ⟨M, hM⟩ := hM
    use fun _ => M
    refine ⟨fun _ => hM, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
