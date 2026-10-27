import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEndBlocks
import AFTD.Kb.Tcs.CyclePowerTerminalBlocks
import AFTD.Kb.Tcs.CyclePowerAlignedTerminalBlocksEndpointOverlap

/-!
# cycle_power_aligned_terminal_blocks_label_period

Topic: combinatorics   Node: c1e190e6d210

Provenance: helper lemma. Uniform conditional profile-rigidity helper for OP-205 / RT-1, following arXiv:2610.15635 Section 3. Arbitrary covers are not classified and no graph covering bound or research advance is claimed.

For nested aligned terminal profiles, complete palettes and separation of equally labelled classes force label period equal to the full radius.
-/

theorem cycle_power_aligned_terminal_blocks_label_period
    {α : Type*} (R c : ℤ) (side : Bool) (w : ℤ → ℤ) (σ : ℤ → α)
    (hR : 0 < R) (hpos : ∀ p, 0 < w p) (hbound : ∀ p, w p ≤ R)
    (hdiv : ∀ p, 2 * w p ∣ 4 * R)
    (hchain : ∀ p q, w p = w q ∨ 2 * w p ∣ w q ∨ 2 * w q ∣ w p)
    (halign : ∀ p, w p ∣ p + c)
    (hodd : ∀ p, w p < R → 2 * w p ∣ p + c - w p)
    (hwperiod : ∀ p, w (p + 4 * R) = w p)
    (hslots : ∀ (v : ℤ) (a : α), ∃ p, cycle_power_terminal_blocks R (w p) p v side ∧ σ p = a)
    (hsep : ∀ (p q u : ℤ), p ≠ q → cycle_power_terminal_blocks R (w p) p u side →
      cycle_power_terminal_blocks R (w q) q u side → σ p ≠ σ q) :
    ∀ p, σ (p + 4 * R) = σ p := by
  intro p
  obtain ⟨q, hq, hσ⟩ := hslots (p + 4 * R - 1) (σ (p + 4 * R))
  by_cases hqp : q = p
  · subst q
    exact hσ.symm
  have hqnew : q ≠ p + 4 * R := by
    intro he
    subst q
    have hb := hbound (p + 4 * R)
    have hp := hpos (p + 4 * R)
    unfold cycle_power_terminal_blocks at hq
    split_ifs at hq with hw hs
    all_goals try { unfold cycle_power_end_blocks at hq }
    all_goals rcases hq with hq | hq <;> omega
  obtain ⟨u, hqu, hnewu⟩ := cycle_power_aligned_terminal_blocks_endpoint_overlap R (w p) (w q)
    p q c side hR (hpos p) (hpos q) (hbound p) (hbound q) (hdiv p) (hdiv q)
    (hchain p q) (halign p) (hodd p) (halign q) (hodd q) hq hqp
  have hnew : cycle_power_terminal_blocks R (w (p + 4 * R)) (p + 4 * R) u side := by
    rw [hwperiod p]
    exact hnewu
  exact False.elim ((hsep q (p + 4 * R) u hqnew hqu hnew) hσ)
