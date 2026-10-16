import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphApexOverBidirectedCompleteEdgeCount
import AFTD.Kb.Tcs.DigraphApexOverBidirectedCompleteOutDegree
import AFTD.Kb.Tcs.DigraphApexOverBidirectedCompleteMinCutLe

/-!
# digraph_min_cut_additive_bound_fails_for_every_d

Topic: graphs   Node: cff678584552

Provenance: original. Related work: arXiv:2610.21381 (Optimally large cuts in both directions), Theorem 1.1 (the bound ⌈((d − 1)m + d²)/(2(2d − 1))⌉ for all sufficiently large m) and the remark in Sec. 6 that it fails for d = 2, m = 9.

For every d ≥ 2 there is a loopless digraph with minimum outdegree at least d and m = (d + 1)² arcs in which every vertex bipartition A ⊔ B has min(e(A, B), e(B, A)) < ⌈((d − 1)m + d²)/(2(2d − 1))⌉. So the bound of Theorem 1.1 of arXiv:2610.21381 does not hold for all m, for any d (the paper notes this only for d = 2, m = 9).
-/

theorem digraph_min_cut_additive_bound_fails_for_every_d (d : ℕ) (hd : 2 ≤ d) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
      (∀ v, ¬ G.Adj v v) ∧ (∀ v, d ≤ (Finset.univ.filter (G.Adj v)).card) ∧
      digraph_edge_count G = (d + 1) ^ 2 ∧
      ∀ A : Finset V, min (digraph_cut_count G A Aᶜ) (digraph_cut_count G Aᶜ A) <
        ⌈((d - 1 : ℚ) * digraph_edge_count G + d ^ 2) / (2 * (2 * d - 1))⌉₊ := by
  letI inst : DecidableRel (digraph_apex_over_bidirected_complete d).Adj := fun u v => by
    unfold digraph_apex_over_bidirected_complete; infer_instance
  refine ⟨Fin (d + 2), inferInstance, inferInstance, digraph_apex_over_bidirected_complete d, inst,
    fun v h => h.1 rfl, digraph_apex_over_bidirected_complete_out_degree d,
    digraph_apex_over_bidirected_complete_edge_count d, fun A => ?_⟩
  refine lt_of_le_of_lt (digraph_apex_over_bidirected_complete_min_cut_le d A) ?_
  rw [digraph_apex_over_bidirected_complete_edge_count d, Nat.lt_ceil]
  have hk : 4 * ((d + 1) ^ 2 / 4) ≤ (d + 1) ^ 2 := Nat.mul_div_le _ _
  have hd' : (3 : ℚ) ≤ 2 * d - 1 := by
    have : (2 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  rw [lt_div_iff₀ (by linarith)]
  rcases Nat.eq_or_lt_of_le hd with h2 | h3
  · subst h2; norm_num
  · have hk' : (4 : ℚ) * (((d + 1) ^ 2 / 4 : ℕ) : ℚ) ≤ ((d : ℚ) + 1) ^ 2 := by exact_mod_cast hk
    have h3' : (3 : ℚ) ≤ d := by exact_mod_cast h3
    have hm := mul_le_mul_of_nonneg_right hk' (by linarith : (0 : ℚ) ≤ 2 * d - 1)
    push_cast
    nlinarith
