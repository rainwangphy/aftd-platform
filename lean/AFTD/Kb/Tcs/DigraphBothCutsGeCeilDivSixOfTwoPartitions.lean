import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_both_cuts_ge_ceil_div_six_of_two_partitions

Topic: graphs   Node: 7b48bba5fa56

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

If two vertex partitions have combined crossing count at least m and combined absolute directed-cut imbalance at most m/3, one partition has both directed cut counts at least the natural ceiling of m/6.
-/

theorem digraph_both_cuts_ge_ceil_div_six_of_two_partitions {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (A₀ A₁ : Finset V)
    (htotal : (digraph_edge_count G : ℚ) ≤
      (digraph_cut_count G A₀ A₀ᶜ : ℚ) + digraph_cut_count G A₀ᶜ A₀ +
      digraph_cut_count G A₁ A₁ᶜ + digraph_cut_count G A₁ᶜ A₁)
    (hbalance : |(digraph_cut_count G A₀ A₀ᶜ : ℚ) - digraph_cut_count G A₀ᶜ A₀| +
      |(digraph_cut_count G A₁ A₁ᶜ : ℚ) - digraph_cut_count G A₁ᶜ A₁| ≤
        (digraph_edge_count G : ℚ) / 3) :
    ∃ A : Finset V, ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G A Aᶜ ∧
      ⌈(digraph_edge_count G : ℚ) / 6⌉₊ ≤ digraph_cut_count G Aᶜ A := by
  let x : ℚ := digraph_cut_count G A₀ A₀ᶜ
  let y : ℚ := digraph_cut_count G A₀ᶜ A₀
  let u : ℚ := digraph_cut_count G A₁ A₁ᶜ
  let v : ℚ := digraph_cut_count G A₁ᶜ A₁
  have hmin (a b : ℚ) : 2 * min a b = a + b - |a-b| := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hgood : (digraph_edge_count G : ℚ) / 6 ≤ min x y ∨
      (digraph_edge_count G : ℚ) / 6 ≤ min u v := by
    by_contra h
    push_neg at h
    have h₀ := hmin x y
    have h₁ := hmin u v
    change (digraph_edge_count G : ℚ) ≤ x+y+u+v at htotal
    change |x-y| + |u-v| ≤ (digraph_edge_count G : ℚ)/3 at hbalance
    linarith
  rcases hgood with h | h
  · refine ⟨A₀, Nat.ceil_le.mpr ?_, Nat.ceil_le.mpr ?_⟩
    · exact h.trans (min_le_left x y)
    · exact h.trans (min_le_right x y)
  · refine ⟨A₁, Nat.ceil_le.mpr ?_, Nat.ceil_le.mpr ?_⟩
    · exact h.trans (min_le_left u v)
    · exact h.trans (min_le_right u v)
