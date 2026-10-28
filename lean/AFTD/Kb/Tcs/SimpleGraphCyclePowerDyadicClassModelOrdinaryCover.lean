import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverEdgeSpan
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassSpanning
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt

/-!
# simple_graph_cycle_power_dyadic_class_model_ordinary_cover

Topic: combinatorics   Node: cbbba1428fd9

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

For every distance 1 ≤ d < 2^m and every integer vertex v there is a rooted offset a < 2^m - d whose class is active at both v-a and v-a+d.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Ordinary coverage: every edge at distance d < 2^m lies inside a single rooted class of the optimal dyadic cover. -/
theorem simple_graph_cycle_power_dyadic_class_model_ordinary_cover
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v)
    (ell : ℤ → Fin (m + 1))
    (hellroot : ∀ p : ℤ,
      c (ell p) ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c (ell p) (p : ZMod n))
    (helluniq : ∀ (p : ℤ) (s : Fin (m + 1)),
      c s ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c s (p : ZMod n) → s = ell p)
    (d : ℕ) (hd : 1 ≤ d) (hdm : d < 2 ^ m) (v : ℤ) :
    ∃ a : ℕ, a < 2 ^ m - d ∧
      decide (a < 2 ^ m ∧
        c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + (a : ZMod n)) =
          c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n))) = true ∧
      decide (a + d < 2 ^ m ∧
        c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + ((a + d : ℕ) : ZMod n)) =
          c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n))) = true := by
  classical
  have hkn : 2^m-1 < n := by omega
  have hadj : (simple_graph_cycle_power n (2^m-1)).Adj
      (v : ZMod n) ((v : ZMod n)+(d : ZMod n)) := by
    apply (simple_graph_cycle_power_adj_iff_of_bandwidth_lt n (2^m-1) hkn _ _).mpr
    refine ⟨(d : ℤ), by omega, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (d : ℤ))]
      exact_mod_cast (show d ≤ 2^m-1 by omega)
    · push_cast
      rfl
  obtain ⟨s, hs⟩ := hcov _ _ hadj
  obtain ⟨a, ha, hra, hend⟩ := simple_graph_cycle_power_dyadic_cover_class_spanning
    m n hm hn c hc hcov s (v : ZMod n)
  have hspan := simple_graph_cycle_power_dyadic_cover_edge_span m n hn (c s) (hc s)
    (v : ZMod n) d hd hdm hs a ha hra hend
  have he : s = ell (v-(a : ℤ)) := helluniq (v-(a : ℤ)) s
    (by simpa only [Int.cast_sub, Int.cast_natCast] using hend.symm)
  have hv : ((v-(a : ℤ) : ℤ) : ZMod n)+(a : ZMod n) = (v : ZMod n) := by push_cast; ring
  refine ⟨a, hspan.1, ?_, ?_⟩
  · apply decide_eq_true
    refine ⟨by omega, ?_⟩
    rw [← he, hv]
    simpa only [Int.cast_sub, Int.cast_natCast] using hra.symm
  · apply decide_eq_true
    refine ⟨by omega, ?_⟩
    rw [← he]
    simpa only [Int.cast_sub, Int.cast_natCast] using hspan.2.symm
