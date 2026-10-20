import AFTD.Prelude
import AFTD.Kb.Tcs.IsKTight
import AFTD.Kb.Tcs.GStableKneser

/-!
# is_k_tight_cycle_sum_unit_iff

Topic: graphs   Node: 0ee7aac01802

Provenance: helper lemma. arXiv:2610.17884 Sec. 1 -- The chromatic number of G-stable Kneser graphs

For k ≥ 3 and m ≥ 4*k - 3, the disjoint sum of the m-cycle and an isolated vertex is k-tight if and only if the chromatic number of its G-stable Kneser graph equals m - 2*k + 3.
-/

/-- The disjoint sum of an m-cycle and an isolated vertex is k-tight if and only if the chromatic number of its G-stable Kneser graph is m - 2*k + 3. -/
theorem is_k_tight_cycle_sum_unit_iff (k m : ℕ) (hk : 3 ≤ k) (hm : 4 * k - 3 ≤ m) :
    is_k_tight ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k ↔
    (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber =
      m - 2 * k + 3 := by
  have h2k : 2 * k ≤ m := by omega
  rw [is_k_tight]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  have harith : (m + 1) - 2 * k + 2 = m - 2 * k + 3 := by omega
  rw [harith]
  have hcast : (↑(m - 2 * k + 3) : ℕ∞) = ↑m - 2 * ↑k + 3 := by
    push_cast [h2k]
    ring
  rw [hcast]
