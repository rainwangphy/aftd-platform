import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# girth_parent_charge_weight_bound

Topic: combinatorics   Node: ca5158c99d8e

Provenance: helper lemma. Girth-dependent center budget for the four-cycle campaign; experiment 13474.

A charged subset of m parents satisfying the girth-dependent proper-subset condition has the displayed weighted parent-plus-charge bound.
-/

theorem girth_parent_charge_weight_bound (g m c : ℕ)
    (hg : 3 ≤ g) (hm : 2 ≤ m) (hc : c ≤ m)
    (hshort : m < g → c < m) :
    (g - 1) * (m + c) ≤ 2 * g * (m - 1) + (g + 1 - 2 * m) := by
  have hg1 : (g - 1) + 1 = g := by omega
  have hm1 : (m - 1) + 1 = m := by omega
  have hp1 : (g - 1) * m + m = g * m := by
    calc
      (g - 1) * m + m = ((g - 1) + 1) * m := by simp [Nat.add_mul]
      _ = g * m := by rw [hg1]
  have hp2 : (g - 1) * (m - 1) + (m - 1) = g * (m - 1) := by
    calc
      (g - 1) * (m - 1) + (m - 1) = ((g - 1) + 1) * (m - 1) := by simp [Nat.add_mul]
      _ = g * (m - 1) := by rw [hg1]
  have hp3 : g * (m - 1) + g = g * m := by
    calc
      g * (m - 1) + g = g * ((m - 1) + 1) := by simp [Nat.mul_add]
      _ = g * m := by rw [hm1]
  by_cases hmg : m < g
  · have hc' : c ≤ m - 1 := by have := hshort hmg; omega
    have hscale := Nat.mul_le_mul_left (g - 1) hc'
    have hcorr : g + 1 ≤ 2 * m + (g + 1 - 2 * m) := by omega
    nlinarith [hp1,hp2,hp3]
  · have hge : g ≤ m := by omega
    have hscale := Nat.mul_le_mul_left (g - 1) hc
    nlinarith [hp1,hp3]
