import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEndBlocks
import AFTD.Kb.Tcs.CyclePowerAlignedEndBlocksEndpointOverlap

/-!
# cycle_power_aligned_end_blocks_label_period

Topic: combinatorics   Node: ca6078431294

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

In an aligned nested end-block family of arbitrary arc length, complete palettes at each vertex and separation of classes sharing a label force label period equal to the arc length.
-/

open Finset

theorem cycle_power_aligned_end_blocks_label_period
    {α : Type*} (D c : ℤ) (w : ℤ → ℤ) (σ : ℤ → α)
    (hpos : ∀ p, 0 < w p) (hbound : ∀ p, 2 * w p ≤ D)
    (hdiv : ∀ p, 2 * w p ∣ D)
    (hchain : ∀ p q, w p = w q ∨ 2 * w p ∣ w q ∨ 2 * w q ∣ w p)
    (halign : ∀ p, w p ∣ p + c)
    (hodd : ∀ p, 2 * w p < D → 2 * w p ∣ p + c - w p)
    (hwperiod : ∀ p, w (p + D) = w p)
    (hslots : ∀ (v : ℤ) (a : α), ∃ p, cycle_power_end_blocks D (w p) p v ∧ σ p = a)
    (hsep : ∀ (p q u : ℤ), p ≠ q →
      cycle_power_end_blocks D (w p) p u → cycle_power_end_blocks D (w q) q u → σ p ≠ σ q) :
    ∀ p, σ (p + D) = σ p := by
  intro p
  obtain ⟨q, hq, hσ⟩ := hslots (p + D - 1) (σ (p + D))
  by_cases hqp : q = p
  · subst q
    exact hσ.symm
  have hqnew : q ≠ p + D := by
    intro he
    subst q
    have hb := hbound (p + D)
    have hp := hpos (p + D)
    unfold cycle_power_end_blocks at hq
    rcases hq with hq | hq <;> omega
  obtain ⟨u, hqu, hnewu⟩ := cycle_power_aligned_end_blocks_endpoint_overlap D (w p) (w q) p q c
    (hpos p) (hpos q) (hbound p) (hbound q) (hdiv p) (hdiv q)
    (hchain p q) (halign p) (hodd p) (halign q) (hodd q) hq hqp
  have hnew : cycle_power_end_blocks D (w (p + D)) (p + D) u := by
    rw [hwperiod p]
    exact hnewu
  exact False.elim ((hsep q (p + D) u hqnew hqu hnew) hσ)
