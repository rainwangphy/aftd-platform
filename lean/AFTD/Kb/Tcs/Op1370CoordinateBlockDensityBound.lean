import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.Op1370CoordinatePatternsBound
import AFTD.Kb.Tcs.Op1370BlockForcesCoordinatePattern

/-!
# op1370_coordinate_block_density_bound

Topic: combinatorics   Node: b8475da16ce8

Provenance: original. Related work: A coordinate-blocker density bound related to Conjecture 4.3 of arXiv:2611.12199.

Let t uncomplemented mutually strongly incomparable families of subsets of Fin n be given. Fix x and, for each color, a k-element set Y of coordinates other than x. Suppose that, for each nonempty color and each y in its set Y, both {x,y} and its complement occur outside that color. Then the total size is at most t times 2^(n-(k+1)).
-/

theorem op1370_coordinate_block_density_bound (n t k : ℕ)
    (𝒜 : Fin t → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
    (hu : ∀ i, is_uncomplemented (𝒜 i)) (x : Fin n) (Y : Fin t → Finset (Fin n))
    (hxY : ∀ i, x ∉ Y i) (hcard : ∀ i, (Y i).card = k)
    (hblock : ∀ i : Fin t, (𝒜 i).Nonempty → ∀ y ∈ Y i,
      ∃ j l : Fin t, j ≠ i ∧ l ≠ i ∧ ({x,y} : Finset (Fin n)) ∈ 𝒜 j ∧ ({x,y} : Finset (Fin n))ᶜ ∈ 𝒜 l) :
    ∑ i, (𝒜 i).card ≤ t * 2 ^ (n - (k + 1)) := by
  open Finset in
  classical
  have hb : ∀ i, (𝒜 i).card ≤ 2 ^ (n - (k + 1)) := by
    intro i
    have hh := op1370_coordinate_patterns_bound n (𝒜 i) (hu i) x (Y i) (hxY i) (by
      intro S hS y hy
      obtain ⟨j, l, hji, hli, hw, hc⟩ := hblock i ⟨S, hS⟩ y hy
      exact op1370_block_forces_coordinate_pattern n t 𝒜 hinc i j l hji hli x y hw hc S hS)
    simpa [hcard i] using hh
  calc
    ∑ i, (𝒜 i).card ≤ ∑ _i : Fin t, 2 ^ (n - (k + 1)) := sum_le_sum (by intro i hi; exact hb i)
    _ = t * 2 ^ (n - (k + 1)) := by simp
