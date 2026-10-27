import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneRootSeparation
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicFullPruneOuter
import AFTD.Kb.Tcs.CyclePowerDyadicHalfOwnerFullPruneOfMiddle
import AFTD.Kb.Tcs.CyclePowerDyadicHalfOwnerOrderOfMiddleFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_half_monotone_of_middle_full_prune

Topic: combinatorics   Node: c95ab6db764a

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

One uniform induction step: if all middle marks have full prunes and both retained outer quarters are monotone toward their endpoints, then the entire left and right halves are monotone toward the endpoints. Tightness, exact dyadic ownership and ordinary coverage are assumed; no counts, period or pre-existing original no-island shape are used.
-/

open Finset

theorem cycle_power_dyadic_half_monotone_of_middle_full_prune
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hleft : ∀ (p : ℤ) (a b : ℕ), a ≤ b → b < 2^k →
      x p b = true → x p a = true)
    (hright : ∀ (p : ℤ) (a b : ℕ), 3*2^k ≤ a → a ≤ b → b < 2^(k+2) →
      x p a = true → x p b = true)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+2) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(k+2)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true) :
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(k+1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 2^(k+1) ≤ a → a ≤ b → b < 2^(k+2) →
        x p a = true → x p b = true) := by
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  have hfull := cycle_power_dyadic_half_owner_full_prune_of_middle k x hmid
  have horder := cycle_power_dyadic_half_owner_order_of_middle_full_prune k x
    htight hexact hmid hleft hright (hcover (2^(k+1)+1) (by omega) (by omega))
  have hstepL (p : ℤ) (i : ℕ) (hi : i+1 < 2^(k+1))
      (hx : x p (i+1) = true) : x p i = true := by
    by_cases hil : i+1 < q
    · exact hleft p i (i+1) (by omega) hil hx
    have hpf := hmid p (i+1) (by omega) (by omega) hx
    have hout := cycle_power_dyadic_full_prune_outer k (x p) hpf
    by_cases hiq : i < q
    · exact hout.1 i hiq
    have hp := (cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)).1
      (i+1) (by omega) hi hx
    obtain ⟨b,hb,hb0,hb1⟩ := hcover (2^(k+1)) (by omega) (by omega) (p+(i : ℤ))
    have hbH : b < 2^(k+1) := by omega
    have hrt : p+(i : ℤ)+1-((i+1 : ℕ) : ℤ)=p := by omega
    have hle := horder (p+(i : ℤ)) b (i+1) hbH hi hb0 hb1
      (by simpa only [hrt] using hx) (by simpa only [hrt] using hp)
    have hib : i ≤ b := by omega
    have hbf := hfull (p+(i : ℤ)-(b : ℤ)) b hbH hb0 hb1
    have hbi : b=i := by
      by_contra hne
      let s := b-i
      have hs : 0 < s := by dsimp [s]; omega
      have hroot : p+(i : ℤ)-(b : ℤ)+(s : ℤ)=p := by dsimp [s]; omega
      have hsep := cycle_power_dyadic_full_prune_root_separation k x
        (hexact k (by omega)) (p+(i : ℤ)-(b : ℤ)) s hs hbf
        (by simpa only [hroot] using hpf)
      dsimp [s] at hsep
      omega
    subst b
    simpa using hb0
  have hstepR (p : ℤ) (i : ℕ) (hi0 : 2^(k+1) ≤ i) (hi1 : i+1 < 2^(k+2))
      (hx : x p i = true) : x p (i+1) = true := by
    by_cases hir : 3*q ≤ i
    · exact hright p i (i+1) hir (by omega) hi1 hx
    have hpf := hmid p i (by omega) (by omega) hx
    have hout := cycle_power_dyadic_full_prune_outer k (x p) hpf
    by_cases hit : 3*q ≤ i+1
    · exact hout.2 (i+1) hit hi1
    let a := i-2^(k+1)
    have ha : a < q := by dsimp [a]; omega
    have hai : a+2^(k+1)=i := by dsimp [a]; omega
    have hp := (cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)).2
      i hi0 (by omega) hx
    have hpa : x p a = true := hp
    have hpH : x p (a+2^(k+1)) = true := by simpa only [hai] using hx
    obtain ⟨b,hb,hb0,hb1⟩ := hcover (2^(k+1)) (by omega) (by omega) (p+(a : ℤ)+1)
    have hbH : b < 2^(k+1) := by omega
    have hrt : p+(a : ℤ)-(a : ℤ)=p := by omega
    have hle := horder (p+(a : ℤ)) a b (by omega) hbH
      (by simpa only [hrt] using hpa) (by simpa only [hrt] using hpH) hb0 hb1
    have hbf := hfull (p+(a : ℤ)+1-(b : ℤ)) b hbH hb0 hb1
    have hba : b=a+1 := by
      by_contra hne
      let s := a+1-b
      have hs : 0 < s := by dsimp [s]; omega
      have hroot : p+(s : ℤ)=p+(a : ℤ)+1-(b : ℤ) := by dsimp [s]; omega
      have hsep := cycle_power_dyadic_full_prune_root_separation k x
        (hexact k (by omega)) p s hs hpf
        (by simpa only [hroot] using hbf)
      dsimp [s] at hsep
      omega
    have hroot : p+(a : ℤ)+1-(b : ℤ)=p := by omega
    have hindex : b+2^(k+1)=i+1 := by omega
    simpa only [hroot,hindex] using hb1
  intro p
  constructor
  · intro a b hab hb hx
    have hmove (b : ℕ) (hab : a ≤ b) : b < 2^(k+1) → x p b = true → x p a = true := by
      induction b,hab using Nat.le_induction with
      | base => intro _ hx; exact hx
      | succ b hab ih =>
        intro hb hx
        exact ih (by omega) (hstepL p b hb hx)
    exact hmove b hab hb hx
  · intro a b ha hab hb hx
    have hmove (b : ℕ) (hab : a ≤ b) : b < 2^(k+2) → x p b = true := by
      induction b,hab using Nat.le_induction with
      | base => intro _; exact hx
      | succ b hab ih =>
        intro hb
        exact hstepR p b (by omega) hb (ih (by omega))
    exact hmove b hab hb
