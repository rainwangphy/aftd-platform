import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverEdgeSpan
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverFibreEndpointUnique
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverTightLongEdges
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelDisjointColours
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicClassModelOrdinaryCover

/-!
# simple_graph_cycle_power_dyadic_class_model_exact_dyadic

Topic: combinatorics   Node: 9c870764208c

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

For every j < m and every integer vertex v there is exactly one offset a < 2^j such that the rooted class at a from v is active at both a and a+(2^m-2^j).
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Exact dyadic coverage: for each j < m and each vertex, exactly one rooted class is active at both offsets a and a+(2^m-2^j). -/
theorem simple_graph_cycle_power_dyadic_class_model_exact_dyadic
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
    (j : ℕ) (hj : j < m) (v : ℤ) :
    (Finset.range (2 ^ j)).sum (fun a =>
      (decide (a < 2 ^ m ∧
          c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + (a : ZMod n)) =
            c (ell (v - (a : ℤ))) ((v - (a : ℤ) : ℤ) : ZMod n)) &&
        decide (a + 2 ^ m - 2 ^ j < 2 ^ m ∧
          c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + ((a + 2 ^ m - 2 ^ j : ℕ) : ZMod n)) =
            c (ell (v - (a : ℤ))) ((v - (a : ℤ) : ℤ) : ZMod n))).toNat) = 1 := by
  classical
  let D := 2^m
  let R := 2^j
  let d := D-R
  have hRD : R < D := Nat.pow_lt_pow_right (by decide) hj
  have hR : 0 < R := Nat.two_pow_pos j
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdD : d < 2^m := by change D-R < D; omega
  let x : ℤ → ℕ → Bool := fun p a => decide (a < D ∧
    c (ell p) ((p : ZMod n)+(a : ZMod n)) = c (ell p) (p : ZMod n))
  let T : ℕ → Bool := fun a => x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+d)
  have hnat (a : ℕ) : a+2^m-2^j = a+d := by dsimp [D, R, d]; omega
  change (range R).sum (fun a => (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1
  simp_rw [hnat]
  change (range R).sum (fun a => (T a).toNat) = 1
  obtain ⟨a, ha, h0, h1⟩ := simple_graph_cycle_power_dyadic_class_model_ordinary_cover
    m n hm hn c hc hcov ell hellroot helluniq d hd hdD v
  have haR : a < R := by change a < D-(D-R) at ha; omega
  have hTa : T a = true := by simp only [T, x, D] at *; simp only [h0, h1, Bool.true_and]
  have hcovering (b : ℕ) (hTb : T b = true) :
      c (ell (v-(b : ℤ))) (v : ZMod n) =
        c (ell (v-(b : ℤ))) ((v : ZMod n)+(d : ZMod n)) := by
    have hbits : x (v-(b : ℤ)) b = true ∧ x (v-(b : ℤ)) (b+d) = true := Bool.and_eq_true_iff.mp hTb
    have hb0 := (of_decide_eq_true hbits.1).2
    have hb1 := (of_decide_eq_true hbits.2).2
    have hv0 : ((v-(b : ℤ) : ℤ) : ZMod n)+(b : ZMod n) = (v : ZMod n) := by push_cast; ring
    have hv1 : ((v-(b : ℤ) : ℤ) : ZMod n)+((b+d : ℕ) : ZMod n) = (v : ZMod n)+(d : ZMod n) := by push_cast; ring
    rw [hv0] at hb0
    rw [hv1] at hb1
    exact hb0.trans hb1.symm
  have hu : ∃! s : Fin (m+1), c s (v : ZMod n) = c s ((v : ZMod n)+(d : ZMod n)) := by
    have hh := simple_graph_cycle_power_dyadic_cover_tight_long_edges m n hm hn c hc hcov
    by_cases hj0 : j=0
    · subst j
      simpa only [d, D, R, pow_zero] using hh.1 (v : ZMod n)
    · simpa only [d, D, R] using hh.2 j (by omega) hj (v : ZMod n)
  have huniq (b : ℕ) (hb : b < R) (hTb : T b = true) : b=a := by
    have he : ell (v-(b : ℤ)) = ell (v-(a : ℤ)) := hu.unique (hcovering b hTb) (hcovering a hTa)
    have hbitsb := (Bool.and_eq_true_iff.mp hTb).1
    have hbitsa := (Bool.and_eq_true_iff.mp hTa).1
    have hPb := (of_decide_eq_true hbitsb).2
    have hPa := (of_decide_eq_true hbitsa).2
    by_contra hne
    exact (simple_graph_cycle_power_dyadic_class_model_disjoint_colours
      m n hm hn c hc hcov ell hellroot helluniq v b a (by dsimp [D] at hRD; omega)
      (by dsimp [D] at hRD; omega) hne hPb hPa) he
  rw [sum_eq_single a]
  · simp only [hTa, Bool.toNat_true]
  · intro b hb hba
    have he : T b = false := Bool.eq_false_iff.mpr (fun hTb => hba (huniq b (mem_range.mp hb) hTb))
    simp only [he, Bool.toNat_false]
  · intro hnot
    exact (hnot (mem_range.mpr haR)).elim
