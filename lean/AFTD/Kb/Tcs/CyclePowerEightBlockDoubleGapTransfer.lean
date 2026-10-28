import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockGapOwnerTransferAt

/-!
# cycle_power_eight_block_double_gap_transfer

Topic: combinatorics   Node: 3eb7c9a7ecc1

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Conditional on no vertical defects and h-separated active roots, two gap transfers preserve the gap, move the physical selected vertex left by2h and cannot decrease its selected offset t. Equality forces the intermediate root to lie exactly h to the left. All additional hypotheses remain explicit.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_double_gap_transfer
    (h t s : ℕ) (hh : 0 < h) (hts : t < s) (hsq : s < 2*h)
    (x : ℤ → ℕ → Bool) (p : ℤ)
    (hprefix : ∀ p : ℤ, ∀ a b : ℕ, a ≤ b → b < 2*h → x p b = true → x p a = true)
    (hparent : ∀ p a, a < 4*h →
      (a < 2*h → x p (a+12*h) = true → x p a = true) ∧
      (2*h ≤ a → x p a = true → x p (a+12*h) = true))
    (h6 : ∀ v : ℤ, (range (4*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+12*h)).toNat) = 1)
    (h7 : ∀ v : ℤ, (range (2*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+14*h)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 16*h → ∀ v : ℤ,
      ∃ a : ℕ, a < 16*h-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hnov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (hsep : ∀ (p r : ℤ) (a b : ℕ), p < r → a < 2*h → b < 2*h →
      x p a = true → x p (14*h+a) = true →
      x r b = true → x r (14*h+b) = true → (h : ℤ) ≤ r-p)
    (hroot : x p t = true) (hchild : x p (2*h+t) = true) (hmiss : x p s = false) :
    ∃ u v : ℕ, u < s-t ∧ v < 2*h-(s-t) ∧ t ≤ v ∧
      x (p+(s : ℤ)-(2*h : ℕ)-(u : ℤ)) u = true ∧
      x (p+(s : ℤ)-(2*h : ℕ)-(u : ℤ)) (2*h+u) = true ∧
      x (p+(s : ℤ)-(2*h : ℕ)-(u : ℤ)) (2*h+u-(s-t)) = false ∧
      x (p+(t : ℤ)-(2*h : ℕ)-(v : ℤ)) v = true ∧
      x (p+(t : ℤ)-(2*h : ℕ)-(v : ℤ)) (2*h+v) = true ∧
      x (p+(t : ℤ)-(2*h : ℕ)-(v : ℤ)) (v+s-t) = false ∧
      (v=t → u+h=s) := by
  have hf (r : ℤ) (a b : ℕ) (hab : a < b) (hb : b < 2*h)
      (ha : x r a = true) (hc : x r (2*h+a) = true) (hm : x r b = false) :
      ∃ u : ℕ, u < b-a ∧
        x (r+(b : ℤ)-(2*h : ℕ)-(u : ℤ)) (2*h+u) = true ∧
        x (r+(b : ℤ)-(2*h : ℕ)-(u : ℤ)) (14*h+u) = true ∧
        x (r+(b : ℤ)-(2*h : ℕ)-(u : ℤ)) (2*h+u-(b-a)) = false := by
    have hp : ∀ p a, a < 2*(2*h) →
      (a < 2*h → x p (a+6*(2*h)) = true → x p a = true) ∧
      (2*h ≤ a → x p a = true → x p (a+6*(2*h)) = true) := by
      simpa only [show 2*(2*h)=4*h by omega,show 6*(2*h)=12*h by omega] using hparent
    have he6 : ∀ v : ℤ, (range (2*(2*h))).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+6*(2*h))).toNat) = 1 := by
      simpa only [show 2*(2*h)=4*h by omega,show 6*(2*h)=12*h by omega] using h6
    have he7 : ∀ v : ℤ, (range (2*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+7*(2*h))).toNat) = 1 := by
      simpa only [show 7*(2*h)=14*h by omega] using h7
    have hc' : ∀ d : ℕ, 1 ≤ d → d < 8*(2*h) → ∀ v : ℤ,
      ∃ a : ℕ, a < 8*(2*h)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true := by
      simpa only [show 8*(2*h)=16*h by omega] using hcover
    simpa only [show 7*(2*h)=14*h by omega] using
      cycle_power_eight_block_gap_owner_transfer_at (2*h) a b (by omega) hab hb x r hprefix hp he6 he7 hc' ha hc hm
  obtain ⟨u,hu,hC,hB,hM⟩ := hf p t s hts hsq hroot hchild hmiss
  let p₁ : ℤ := p+(s : ℤ)-(2*h : ℕ)-(u : ℤ)
  let s₁ := 2*h+u-(s-t)
  have huq : u < 2*h := by omega
  have hus : u < s₁ := by dsimp [s₁]; omega
  have hs₁ : s₁ < 2*h := by dsimp [s₁]; omega
  have hAu : x p₁ u = true := hnov p₁ u huq hC
  obtain ⟨v,hv,hC₂,hB₂,hM₂⟩ := hf p₁ u s₁ hus hs₁ hAu hC hM
  let p₂ : ℤ := p₁+(s₁ : ℤ)-(2*h : ℕ)-(v : ℤ)
  have hvq : v < 2*h := by omega
  have hAv : x p₂ v = true := hnov p₂ v hvq hC₂
  have hp₁ : p₁ < p := by dsimp [p₁]; omega
  have hp₂ : p₂ < p₁ := by dsimp [p₂]; omega
  have hBt : x p (14*h+t) = true := by
    have ht := (hparent p (2*h+t) (by omega)).2 (by omega) hchild
    convert ht using 1 <;> congr 1 <;> omega
  have hs1 := hsep p₁ p u t hp₁ huq (by omega) hAu hB hroot hBt
  have hs2 := hsep p₂ p₁ v u hp₂ hvq huq hAv hB₂ hAu hB
  have heP : p₂=p+(t : ℤ)-(2*h : ℕ)-(v : ℤ) := by dsimp [p₂,p₁,s₁]; omega
  have heM : 2*h+v-(s₁-u)=v+s-t := by dsimp [s₁]; omega
  refine ⟨u,v,hu,by dsimp [s₁] at hv; omega,?_,hAu,hC,hM,?_,?_,?_,?_⟩
  · dsimp [p₁,p₂,s₁] at hs1 hs2
    omega
  · simpa only [← heP] using hAv
  · simpa only [← heP] using hC₂
  · simpa only [← heP,heM] using hM₂
  · intro hvEq
    dsimp [p₁,p₂,s₁] at hs1 hs2
    omega
