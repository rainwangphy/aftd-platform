import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.FanRamseyBound

/-!
# mixed_diamond_fan_ramsey_bound_base_zero_diamond_colours

Topic: combinatorics   Node: dec77cbe7c88

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Base case a = 0 (b ≥ 1): if d ≥ (j-1)*b + 1 then every colouring of the subsets of Fin d with 0 + b colours has a monochromatic induced F_j in one of the b colours.
-/

/-- Base case a = 0: only fan colours, so this is fan_ramsey_bound up to the Fin (0+b) ≃ Fin b reindexing. -/
theorem mixed_diamond_fan_ramsey_bound_base_zero_diamond_colours (j b d : ℕ) (hj : 2 ≤ j)
    (hb : 1 ≤ b) (hd : (j - 1) * b + 1 ≤ d) : mixed_ramsey_property j 0 b d := by
  intro χ
  right
  have hk : 1 ≤ 0 + b := by omega
  have hcard : (0 + b) * (j - 1) + 1 ≤ Fintype.card (Fin d) := by
    rw [Fintype.card_fin, Nat.zero_add, Nat.mul_comm]
    exact hd
  have h := fan_ramsey_bound_general j hj (0 + b) hk (Fin d) hcard χ
  rcases h with ⟨col, top, htop, mid, hmid, hinc⟩
  have hcol : ∃ col' : Fin b, Fin.natAdd 0 col' = col := by
    use ⟨col.val, by omega⟩
    ext
    simp
  rcases hcol with ⟨col', rfl⟩
  refine ⟨col', top, htop, mid, hmid, hinc⟩
