import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193CubicNoncolorableIfCycleLower
import AFTD.Kb.Tcs.Op193CycleIsolatedVertexKTightIffGe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_193_cubic_tight_if_cycle_lower

Topic: graphs   Node: 78625d11b9bd

Provenance: helper lemma. Explicit-threshold refinement of arXiv:2610.17884 Section 3.

For k at least 3 and m at least k((k-1)²+1), the stable k-set graph of the m-cycle plus an isolated vertex has chromatic number m-2k+3, provided the cycle-only stable k-set graph has chromatic number at least m-2k+2.
-/

theorem op_193_cubic_tight_if_cycle_lower (k m : ℕ) (hk : 3 ≤ k)
    (hm : k * ((k-1)^2+1) ≤ m)
    (hcycle : ((m-2*k+2 : ℕ) : ℕ∞) ≤ (GStableKneser (SimpleGraph.cycleGraph m) k).chromaticNumber) :
    (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber =
      m-2*k+3 := by
  have hf : 4 ≤ (k-1)^2+1 := by
    have hh : 2 ≤ k-1 := by omega
    nlinarith
  have hm4 : 4*k-3 ≤ m := by
    have hh := Nat.mul_le_mul_left k hf
    omega
  have hnotcycle : ¬ (GStableKneser (SimpleGraph.cycleGraph m) k).Colorable (m-2*k+1) := by
    intro hc
    have hu := hc.chromaticNumber_le
    have hlt : ((m-2*k+1 : ℕ) : ℕ∞) < ((m-2*k+2 : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : m-2*k+1 < m-2*k+2)
    exact (not_le_of_gt hlt) (hcycle.trans hu)
  have hnot := op_193_cubic_noncolorable_if_cycle_lower k m hk hm hnotcycle
  have hlt : ((m-2*k+2 : ℕ) : ℕ∞) <
      (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber := by
    apply lt_of_not_ge
    intro h
    exact hnot ((SimpleGraph.chromaticNumber_le_iff_colorable (n := m-2*k+2)).mp h)
  have hge : (((m-2*k+2)+1 : ℕ) : ℕ∞) ≤
      (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber :=
    ENat.natCast_add_one_le_iff.mpr hlt
  have hn : (m-2*k+2)+1 = m-2*k+3 := by omega
  rw [hn] at hge
  have hN : ((m-2*k+3 : ℕ) : ℕ∞) = (m : ℕ∞)-2*(k : ℕ∞)+3 := by
    rw [ENat.natCast_add, ENat.natCast_sub, ENat.natCast_mul]
    norm_num
  rw [hN] at hge
  exact (op_193_cycle_isolated_vertex_k_tight_iff_ge k m hk hm4).mpr hge
