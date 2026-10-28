import AFTD.Prelude

/-!
# cycle_power_eight_block_stable_overlap

Topic: combinatorics   Node: b933f58367cd

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Definition of a rigid overlap pattern on three roots p,p-h,p-2h with alternating selected offsets t and s-h and the displayed missing offsets. This definition asserts no existence.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def cycle_power_eight_block_stable_overlap (h : ℕ) (x : ℤ → ℕ → Bool) : Prop := ∃ (p : ℤ) (t s : ℕ), t < h ∧ h ≤ s ∧ s < 2*h ∧
    x p t = true ∧ x p (2*h+t) = true ∧ x p s = false ∧
    x (p-(h : ℤ)) (s-h) = true ∧ x (p-(h : ℤ)) (2*h+(s-h)) = true ∧
    x (p-(h : ℤ)) (h+t) = false ∧
    x (p-(2*h : ℕ)) t = true ∧ x (p-(2*h : ℕ)) (2*h+t) = true ∧
    x (p-(2*h : ℕ)) s = false
