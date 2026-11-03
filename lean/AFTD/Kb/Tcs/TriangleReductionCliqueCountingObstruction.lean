import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# triangle_reduction_clique_counting_obstruction

Topic: graphs   Node: 14b5376e5975

Provenance: helper lemma. Counting step toward simple_graph_complete_no_small_vertex_triangle_reduction in the triangle packing-cover campaign.

The displayed natural-number inequalities for the four types of packed triangles, cover size, and uncovered cross edges are inconsistent when k is positive and the outside set has size at least 40k.
-/

theorem triangle_reduction_clique_counting_obstruction
    (k m a b c d x h q : ℕ)
    (hk : 0 < k) (hm : 40 * k ≤ m)
    (hcross : 2 * (a + b) ≤ k * m)
    (hinside : 2 * (b + c) ≤ k * k)
    (hbudget : x ≤ 2 * (a + b + c + d))
    (hpacked : 3 * d ≤ x)
    (hcover : k * m + a + 3 * d ≤ x + h)
    (hmax : h ≤ k * q)
    (hclique : q * (q - 1) ≤ 2 * x) : False := by
  have hx : x ≤ 3 * k * m + 3 * k * k := by nlinarith
  have hsum : k * m ≤ 2 * h + 2 * k * k := by nlinarith
  have hq : m ≤ 2 * q + 2 * k := by
    by_contra hn
    have hp : 0 < k * (m - (2 * q + 2 * k)) := by
      apply Nat.mul_pos hk
      omega
    have heq : k * m = k * (m - (2 * q + 2 * k)) + k * (2 * q + 2 * k) := by
      have hle : 2 * q + 2 * k ≤ m := by omega
      have hc := congrArg (fun t : ℕ => k * t) (Nat.sub_add_cancel hle)
      rw [Nat.mul_add] at hc
      exact hc.symm
    nlinarith
  have hq19 : 19 * k ≤ q := by omega
  have hkq : q ≤ k * q := by nlinarith
  have hkq2 : 19 * k * k ≤ k * q := by nlinarith
  have hqpos : 1 ≤ q := by omega
  have hqsub : q - 1 + 1 = q := by omega
  nlinarith
