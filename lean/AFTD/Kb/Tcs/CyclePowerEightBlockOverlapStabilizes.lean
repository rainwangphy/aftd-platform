import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockDoubleGapTransfer
import AFTD.Kb.Tcs.CyclePowerEightBlockStableOverlap

/-!
# cycle_power_eight_block_overlap_stabilizes

Topic: combinatorics   Node: 76248bb772ad

Provenance: helper lemma. Supporting uniform structural route for OP-205 / RT-1 following arXiv:2610.15635. No unconditional shape theorem or main covering result is claimed. No advance flag.

Under the explicit no-vertical hypothesis and active-root separation, every overlap defect yields the rigid three-root stable-overlap pattern. This is a conditional reduction, not an unconditional extension or graph-covering theorem.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_overlap_stabilizes
    (h : ℕ) (hh : 0 < h) (x : ℤ → ℕ → Bool)
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
    (p : ℤ) (t s : ℕ) (hts : t < s) (hsq : s < 2*h)
    (hroot : x p t = true) (hchild : x p (2*h+t) = true) (hmiss : x p s = false) :
    cycle_power_eight_block_stable_overlap h x := by
  have aux : ∀ N : ℕ, ∀ (p : ℤ) (t s : ℕ), 2*h-t=N → t < s → s < 2*h →
      x p t = true → x p (2*h+t) = true → x p s = false →
      cycle_power_eight_block_stable_overlap h x := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p t s hN hts hsq hroot hchild hmiss
      obtain ⟨u,v,hu,hv,htv,hAu,hCu,hMu,hAv,hCv,hMv,heq⟩ :=
        cycle_power_eight_block_double_gap_transfer h t s hh hts hsq x p
          hprefix hparent h6 h7 hcover hnov hsep hroot hchild hmiss
      by_cases hvEq : v=t
      · have hus : u+h=s := heq hvEq
        have hth : t < h := by omega
        have hhS : h ≤ s := by omega
        refine ⟨p,t,s,hth,hhS,hsq,hroot,hchild,hmiss,?_,?_,?_,?_,?_,?_⟩
        · convert hAu using 1 <;> congr 1 <;> omega
        · convert hCu using 1 <;> congr 1 <;> omega
        · convert hMu using 1 <;> congr 1 <;> omega
        · convert hAv using 1 <;> congr 1 <;> omega
        · convert hCv using 1 <;> congr 1 <;> omega
        · convert hMv using 1 <;> congr 1 <;> omega
      · have htv' : t < v := by omega
        exact ih (2*h-v) (by omega) (p+(t : ℤ)-(2*h : ℕ)-(v : ℤ)) v (v+s-t)
          rfl (by omega) (by omega) hAv hCv hMv
  exact aux (2*h-t) p t s rfl hts hsq hroot hchild hmiss
