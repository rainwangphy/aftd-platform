import AFTD.Prelude
import AFTD.Kb.Tcs.Op193CycleIsolatedVertexChromaticLe
import AFTD.Kb.Tcs.GStableKneser

/-!
# op_193_cycle_isolated_vertex_k_tight_iff_ge

Topic: graphs   Node: 4781e9e134b7

Provenance: helper lemma. arXiv:2610.17884 Sec. 1 -- The chromatic number of G-stable Kneser graphs

For k ≥ 3 and m ≥ 4*k - 3, the chromatic number of the G-stable Kneser graph of the disjoint sum of the m-cycle and an isolated vertex equals m - 2*k + 3 if and only if it is at least m - 2*k + 3.
-/

/-- The chromatic number of the G-stable Kneser graph of C_m ⊔ K_1 equals m - 2*k + 3 if and only if it is at least m - 2*k + 3. -/
theorem op_193_cycle_isolated_vertex_k_tight_iff_ge
    (k m : ℕ) (hk : 3 ≤ k) (hm : 4 * k - 3 ≤ m) :
    (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber =
      m - 2 * k + 3 ↔
    (m - 2 * k + 3 : ℕ∞) ≤ (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber := by
  have hN : ((m - 2 * k + 3 : ℕ) : ℕ∞) = (m : ℕ∞) - 2 * (k : ℕ∞) + 3 := by
    rw [ENat.natCast_add, ENat.natCast_sub, ENat.natCast_mul]
    norm_num
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm
      (by simpa [hN] using op_193_cycle_isolated_vertex_chromatic_le k m hk hm) h
