import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverLayerRootUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverFibreEndpointUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassSpanning
import AFTD.Kb.Tcs.BoolSumEqCardFilter
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelDisjointColours

/-!
# simple_graph_cycle_power_dyadic_class_model_vertex_layers

Topic: combinatorics   Node: 2cbd494f725a

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

For an optimal (m+1)-layer dyadic cover, with ell(p) the unique layer covering the endpoint pair (p, p+2^m-1) and the class of p cut to the arc of length 2^m, exactly m+1 of the rooted classes at a fixed vertex v are active.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Constant active count: exactly m+1 rooted classes are active at each vertex of an optimal dyadic cover. -/
theorem simple_graph_cycle_power_dyadic_class_model_vertex_layers
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
    (v : ℤ) :
    (Finset.range (2 ^ m)).sum (fun a =>
      (decide (a < 2 ^ m ∧
        c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + (a : ZMod n)) =
          c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n)))).toNat) = m + 1 := by
  classical
  let P : ℕ → Prop := fun a => a < 2^m ∧
    c (ell (v-(a : ℤ))) (((v-(a : ℤ) : ℤ) : ZMod n)+(a : ZMod n)) =
      c (ell (v-(a : ℤ))) ((v-(a : ℤ) : ℤ) : ZMod n)
  let S := (range (2^m)).filter (fun a => decide (P a) = true)
  change (range (2^m)).sum (fun a => (decide (P a)).toNat) = m+1
  rw [bool_sum_eq_card_filter]
  change S.card = m+1
  have hcard : S.card = (univ : Finset (Fin (m+1))).card := by
    apply card_bij (s := S) (t := (univ : Finset (Fin (m+1)))) (fun (a : ℕ) _ => ell (v-(a : ℤ)))
    · intro a ha
      exact mem_univ _
    · intro a ha b hb he
      have hPa : P a := by simpa only [decide_eq_true_eq] using (mem_filter.mp ha).2
      have hPb : P b := by simpa only [decide_eq_true_eq] using (mem_filter.mp hb).2
      by_contra hne
      exact (simple_graph_cycle_power_dyadic_class_model_disjoint_colours
        m n hm hn c hc hcov ell hellroot helluniq v a b hPa.1 hPb.1 hne hPa.2 hPb.2) he
    · intro s hs
      obtain ⟨a, ha, hra, hend⟩ := simple_graph_cycle_power_dyadic_cover_class_spanning
        m n hm hn c hc hcov s (v : ZMod n)
      have he : s = ell (v-(a : ℤ)) := helluniq (v-(a : ℤ)) s
        (by simpa only [Int.cast_sub, Int.cast_natCast] using hend.symm)
      have hv : ((v-(a : ℤ) : ℤ) : ZMod n)+(a : ZMod n) = (v : ZMod n) := by push_cast; ring
      have haD : a < 2^m := by
        have hpow := Nat.two_pow_pos m
        omega
      have hPa : P a := by
        refine ⟨haD, ?_⟩
        rw [← he, hv]
        simpa only [Int.cast_sub, Int.cast_natCast] using hra.symm
      refine ⟨a, mem_filter.mpr ⟨mem_range.mpr haD, ?_⟩, he.symm⟩
      simpa only [decide_eq_true_eq] using hPa
  simpa only [card_univ, Fintype.card_fin] using hcard
