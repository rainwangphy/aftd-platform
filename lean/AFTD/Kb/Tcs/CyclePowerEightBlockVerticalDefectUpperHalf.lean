import AFTD.Prelude

/-!
# cycle_power_eight_block_vertical_defect_upper_half

Topic: combinatorics   Node: 3fdfb4f1c7b3

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

For q=2h, the additional third dyadic parent matching forces any vertical C_t-without-A_t defect to satisfy h<=t. The parent hypotheses are explicit.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_vertical_defect_upper_half
    (h : ℕ) (x : ℤ → ℕ → Bool)
    (hparent6 : ∀ p a, a < 4*h →
      (a < 2*h → x p (a+12*h) = true → x p a = true) ∧
      (2*h ≤ a → x p a = true → x p (a+12*h) = true))
    (hparent7 : ∀ p a, a < 2*h →
      (a < h → x p (a+14*h) = true → x p a = true) ∧
      (h ≤ a → x p a = true → x p (a+14*h) = true))
    (p : ℤ) (t : ℕ) (ht : t < 2*h)
    (hchild : x p (2*h+t) = true) (hmiss : x p t = false) : h ≤ t := by
  by_contra hn
  have ht' : t < h := by omega
  have hB : x p (t+14*h) = true := by
    have hc := (hparent6 p (2*h+t) (by omega)).2 (by omega) hchild
    convert hc using 1 <;> congr 1 <;> omega
  have hA := (hparent7 p t ht).1 ht' hB
  rw [hmiss] at hA
  contradiction
