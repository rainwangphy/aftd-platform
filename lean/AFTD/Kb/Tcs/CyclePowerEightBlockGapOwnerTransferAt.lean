import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockGapOwnerTransfer
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent

/-!
# cycle_power_eight_block_gap_owner_transfer_at

Topic: combinatorics   Node: f4d1904113f5

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Translation of the accepted gap-owner transfer to any integer root, with full ordinary coverage supplying the required edge.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_gap_owner_transfer_at
    (q t s : ℕ) (hq : 0 < q) (hts : t < s) (hsq : s < q)
    (x : ℤ → ℕ → Bool) (p : ℤ)
    (hprefix : ∀ p : ℤ, ∀ a b : ℕ, a ≤ b → b < q → x p b = true → x p a = true)
    (hparent : ∀ p a, a < 2*q →
      (a < q → x p (a+6*q) = true → x p a = true) ∧
      (q ≤ a → x p a = true → x p (a+6*q) = true))
    (h6 : ∀ v : ℤ, (range (2*q)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+6*q)).toNat) = 1)
    (h7 : ∀ v : ℤ, (range q).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+7*q)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 8*q → ∀ v : ℤ,
      ∃ a : ℕ, a < 8*q-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hroot : x p t = true) (hchild : x p (q+t) = true) (hmiss : x p s = false) :
    ∃ u : ℕ, u < s-t ∧
      x (p+(s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u) = true ∧
      x (p+(s : ℤ)-(q : ℤ)-(u : ℤ)) (7*q+u) = true ∧
      x (p+(s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u-(s-t)) = false := by
  let y : ℤ → ℕ → Bool := fun r a => x (p+r) a
  have he6 : ∀ v : ℤ, (range (2*q)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+6*q)).toNat) = 1 := by
    intro v
    simpa only [y, add_sub_assoc] using h6 (p+v)
  have he7 : ∀ v : ℤ, (range q).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+7*q)).toNat) = 1 := by
    intro v
    simpa only [y, add_sub_assoc] using h7 (p+v)
  have hc : ∃ a : ℕ, a < q+(s-t) ∧ y ((s : ℤ)-(a : ℤ)) a = true ∧
      y ((s : ℤ)-(a : ℤ)) (a+7*q+t-s) = true := by
    obtain ⟨a, ha, ha₀, ha₁⟩ := hcover (7*q+t-s) (by omega) (by omega) (p+(s : ℤ))
    refine ⟨a, by omega, ?_, ?_⟩
    · simpa only [y, add_sub_assoc] using ha₀
    · have hi : a+(7*q+t-s)=a+7*q+t-s := by omega
      simpa only [y, add_sub_assoc, hi] using ha₁
  obtain ⟨u,hu,hC,hB,hA⟩ := cycle_power_eight_block_gap_owner_transfer q t s hq hts hsq y
    (fun r a b hab hb hx => hprefix (p+r) a b hab hb hx)
    (fun r a ha => hparent (p+r) a ha) he6 he7
    (by simpa only [y,add_zero] using hroot)
    (by simpa only [y,add_zero] using hchild)
    (by simpa only [y,add_zero] using hmiss) hc
  refine ⟨u,hu,?_,?_,?_⟩
  · simpa only [y,add_sub_assoc] using hC
  · simpa only [y,add_sub_assoc] using hB
  · simpa only [y,add_sub_assoc] using hA
