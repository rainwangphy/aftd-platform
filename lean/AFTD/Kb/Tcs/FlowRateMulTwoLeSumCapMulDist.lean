import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.IsMulticommodityFlow

/-!
# flow_rate_mul_two_le_sum_cap_mul_dist

Topic: information   Node: bce482164d59

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

If a fractional multicommodity flow on net supports the common rate r, and d is a symmetric, nonnegative, triangle-satisfying function on V with d(u,u) = 0, then 2*r*(sum over sessions of d(src,tgt)) is at most the sum over all ordered pairs of vertices of cap({u,v})*d(u,v).
-/

/-- Metric (potential) upper bound on the common rate of a fractional multicommodity flow. -/
theorem flow_rate_mul_two_le_sum_cap_mul_dist
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r : ℝ}
    (h : FlowSupportsRate net sess r) (d : V → V → ℝ)
    (h_nonneg : ∀ u v, 0 ≤ d u v) (h_symm : ∀ u v, d u v = d v u)
    (h_diag : ∀ u, d u u = 0) (h_tri : ∀ u v w, d u v ≤ d u w + d w v) :
    2 * r * (∑ k, d (sess.src k) (sess.tgt k)) ≤ ∑ u, ∑ v, net.cap s(u, v) * d u v := by
  open Finset in
  obtain ⟨f, hf⟩ := h
  have h_single : ∀ k : K, r * d (sess.src k) (sess.tgt k) ≤ ∑ v, ∑ w, f k v w * d v w := by
    intro k
    have hdiv := hf.2.2 k
    have hnn := hf.1 k
    set s := sess.src k
    set t := sess.tgt k
    have hst : s ≠ t := sess.src_ne_tgt k
    have h_lhs : (∑ v, (∑ w, f k v w - ∑ u, f k u v) * d s v) = -r * d s t := by
      have h_split : ∀ v, (∑ w, f k v w - ∑ u, f k u v) * d s v =
          (if v = s then r * d s s else 0) + (if v = t then -r * d s t else 0) := by
        intro v
        rw [hdiv v]
        split_ifs <;> (try subst_vars) <;> (try contradiction) <;> ring
      simp_rw [h_split, sum_add_distrib]
      have hd_ss : d s s = 0 := h_diag s
      simp [hd_ss]
    have h_geom : (∑ v, (∑ w, f k v w - ∑ u, f k u v) * d s v) = ∑ v, ∑ w, f k v w * (d s v - d s w) := by
      have h1 : (∑ v, (∑ w, f k v w - ∑ u, f k u v) * d s v) =
          (∑ v, (∑ w, f k v w) * d s v) - (∑ v, (∑ u, f k u v) * d s v) := by
        simp_rw [sub_mul, sum_sub_distrib]
      have h2 : (∑ v, (∑ u, f k u v) * d s v) = ∑ v, ∑ w, f k v w * d s w := by
        simp_rw [sum_mul]
        rw [sum_comm]
      have h3 : (∑ v, (∑ w, f k v w) * d s v) = ∑ v, ∑ w, f k v w * d s v := by
        simp_rw [sum_mul]
      rw [h1, h2, h3]
      simp_rw [← sum_sub_distrib, ← mul_sub]
    have h_le : - ∑ v, ∑ w, f k v w * d v w ≤ ∑ v, ∑ w, f k v w * (d s v - d s w) := by
      rw [← sum_neg_distrib]
      apply sum_le_sum
      intro v _
      rw [← sum_neg_distrib]
      apply sum_le_sum
      intro w _
      have htri : - d v w ≤ d s v - d s w := by
        have := h_tri s w v
        linarith
      have h_nonneg_f : 0 ≤ f k v w := hnn v w
      nlinarith
    rw [← h_geom, h_lhs] at h_le
    linarith

  have h_sum_k : r * (∑ k, d (sess.src k) (sess.tgt k)) ≤ ∑ k, ∑ v, ∑ w, f k v w * d v w := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    exact h_single k

  have h_comm : (∑ k, ∑ v, ∑ w, f k v w * d v w) = ∑ v, ∑ w, ∑ k, f k v w * d v w := by
    rw [sum_comm]
    congr 1
    ext v
    rw [sum_comm]

  have h_pair : 2 * (∑ v, ∑ w, ∑ k, f k v w * d v w) =
      ∑ v, ∑ w, (∑ k, (f k v w + f k w v)) * d v w := by
    have h_two : 2 * (∑ v, ∑ w, ∑ k, f k v w * d v w) =
        (∑ v, ∑ w, ∑ k, f k v w * d v w) + (∑ v, ∑ w, ∑ k, f k v w * d v w) := by ring
    rw [h_two]
    have h_swap : (∑ v, ∑ w, ∑ k, f k v w * d v w) = ∑ v, ∑ w, ∑ k, f k w v * d v w := by
      rw [sum_comm]
      apply sum_congr rfl
      intro w _
      apply sum_congr rfl
      intro v _
      rw [h_symm w v]
    nth_rw 2 [h_swap]
    simp_rw [← sum_add_distrib, ← add_mul, ← sum_mul]

  have h_cap_le : (∑ v, ∑ w, (∑ k, (f k v w + f k w v)) * d v w) ≤ ∑ u, ∑ v, net.cap s(u, v) * d u v := by
    apply sum_le_sum
    intro u _
    apply sum_le_sum
    intro v _
    by_cases huv : u = v
    · subst huv
      rw [h_diag u]
      ring_nf
      rfl
    · have hcap := hf.2.1 u v huv
      have hd := h_nonneg u v
      nlinarith

  calc
    2 * r * (∑ k, d (sess.src k) (sess.tgt k))
      = 2 * (r * ∑ k, d (sess.src k) (sess.tgt k)) := by ring
    _ ≤ 2 * (∑ k, ∑ v, ∑ w, f k v w * d v w) := by nlinarith
    _ = 2 * (∑ v, ∑ w, ∑ k, f k v w * d v w) := by rw [h_comm]
    _ = ∑ v, ∑ w, (∑ k, (f k v w + f k w v)) * d v w := h_pair
    _ ≤ ∑ u, ∑ v, net.cap s(u, v) * d u v := h_cap_le
