import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_eight_block_gap_owner_transfer

Topic: combinatorics   Node: c8d0f02f731e

Provenance: helper lemma. Uniform structural helpers for OP-205 / RT-1, following arXiv:2610.15635. The new eight-block local extension remains unproved. These lemmas retain explicit shape/selected-missing hypotheses and do not settle any graph covering value; no research advance is claimed.

Let t<s<q. Under prefix first eighths, the6q parent implications and exact6q/7q ownership, suppose root0 selects t andq+t but misses s, and edge(s,7q+t) is covered. Some u<s-t gives root s-q-u selecting q+u and7q+u but missing q+u-(s-t). Thus the new overlap gap is q-(s-t). This generalizes the accepted boundary transfer without assuming current4q exactness.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_gap_owner_transfer
    (q t s : ℕ) (hq : 0 < q) (hts : t < s) (hsq : s < q)
    (x : ℤ → ℕ → Bool)
    (hprefix : ∀ p : ℤ, ∀ a b : ℕ, a ≤ b → b < q →
      x p b = true → x p a = true)
    (hparent : ∀ p a, a < 2*q →
      (a < q → x p (a+6*q) = true → x p a = true) ∧
      (q ≤ a → x p a = true → x p (a+6*q) = true))
    (h6 : ∀ v : ℤ, (range (2*q)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+6*q)).toNat) = 1)
    (h7 : ∀ v : ℤ, (range q).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+7*q)).toNat) = 1)
    (hroot : x 0 t = true) (hchild : x 0 (q+t) = true)
    (hmiss : x 0 s = false)
    (hcover : ∃ a : ℕ, a < q+(s-t) ∧ x ((s : ℤ)-(a : ℤ)) a = true ∧
      x ((s : ℤ)-(a : ℤ)) (a+7*q+t-s) = true) :
    ∃ u : ℕ, u < s-t ∧
      x ((s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u) = true ∧
      x ((s : ℤ)-(q : ℤ)-(u : ℤ)) (7*q+u) = true ∧
      x ((s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u-(s-t)) = false := by
  let L := s-t
  have hL₀ : 0 < L := by dsimp [L]; omega
  have hLq : L < q := by dsimp [L]; omega
  have htq : t < q := by omega
  have hB : x 0 (7*q+t) = true := by
    have h := (hparent 0 (q+t) (by omega)).2 (by omega) hchild
    convert h using 1 <;> congr 1 <;> omega
  have h6' : ∀ v : ℤ, (range (2*q)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*q-2*q)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+8*q-2*q=a+6*q := by omega
    simpa only [hi] using h6 v
  have h7' : ∀ v : ℤ, (range q).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*q-q)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+8*q-q=a+7*q := by omega
    simpa only [hi] using h7 v
  obtain ⟨a, ha, ha₀, ha₁⟩ := hcover
  have haq : q ≤ a := by
    by_contra hne
    have haq : a < q := by omega
    by_cases haL : a < L
    · let b := q-L+a
      have hbq : b < q := by dsimp [b]; omega
      have hp : ((q+t : ℕ) : ℤ)-(b : ℤ)=(s : ℤ)-(a : ℤ) := by
        dsimp [b,L]; omega
      have hi : b+6*q=a+7*q+t-s := by dsimp [b,L]; omega
      have hb₁ : x (((q+t : ℕ) : ℤ)-(b : ℤ)) (b+6*q) = true := by
        simpa only [hp,hi] using ha₁
      have hb₀ := (hparent (((q+t : ℕ) : ℤ)-(b : ℤ)) b (by omega)).1 hbq hb₁
      have huniq := cycle_power_exact_pair_unique (8*q) (2*q) x h6'
        ((q+t : ℕ) : ℤ) b (q+t) (by omega) (by omega) hb₀
        (by convert hb₁ using 1 <;> congr 1 <;> omega)
        (by simpa only [sub_self] using hchild)
        (by simpa only [sub_self,show (q+t)+8*q-2*q=7*q+t by omega] using hB)
      omega
    · let b := a-L
      have hbq : b < q := by dsimp [b]; omega
      have hp : (t : ℤ)-(b : ℤ)=(s : ℤ)-(a : ℤ) := by dsimp [b,L]; omega
      have hb₀ : x ((t : ℤ)-(b : ℤ)) b = true := by
        have h := hprefix ((s : ℤ)-(a : ℤ)) b a (by dsimp [b]; omega) haq ha₀
        simpa only [hp] using h
      have hb₁ : x ((t : ℤ)-(b : ℤ)) (b+7*q) = true := by
        have hi : b+7*q=a+7*q+t-s := by dsimp [b,L]; omega
        simpa only [hp,hi] using ha₁
      have huniq := cycle_power_exact_pair_unique (8*q) q x h7'
        (t : ℤ) b t hbq htq hb₀
        (by simpa only [show b+8*q-q=b+7*q by omega] using hb₁)
        (by simpa only [sub_self] using hroot)
        (by simpa only [sub_self,show t+8*q-q=7*q+t by omega] using hB)
      have haeq : a=s := by dsimp [b,L] at huniq; omega
      subst a
      have hlow : x 0 s = true := by simpa only [sub_self] using ha₀
      rw [hmiss] at hlow
      contradiction
  let u := a-q
  have hu : u < s-t := by dsimp [u]; omega
  have haeq : a=q+u := by dsimp [u]; omega
  have hp : (s : ℤ)-(a : ℤ)=(s : ℤ)-(q : ℤ)-(u : ℤ) := by omega
  have hC : x ((s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u) = true := by
    simpa only [← haeq,← hp] using ha₀
  have hB' : x ((s : ℤ)-(q : ℤ)-(u : ℤ)) (7*q+u) = true := by
    have h := (hparent ((s : ℤ)-(q : ℤ)-(u : ℤ)) (q+u) (by omega)).2
      (by omega) hC
    convert h using 1 <;> congr 1 <;> omega
  refine ⟨u, hu, hC, hB', ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hA
  let b := q+u-L
  have hbt : t < b := by dsimp [b,L]; omega
  have hbq : b < q := by dsimp [b,L]; omega
  have hp' : (t : ℤ)-(b : ℤ)=(s : ℤ)-(q : ℤ)-(u : ℤ) := by dsimp [b,L]; omega
  have hb₁ : x ((t : ℤ)-(b : ℤ)) (b+7*q) = true := by
    have hi : b+7*q=a+7*q+t-s := by dsimp [b,L]; omega
    simpa only [hp',hi,← hp] using ha₁
  have huniq := cycle_power_exact_pair_unique (8*q) q x h7'
    (t : ℤ) b t hbq htq
    (by simpa only [hp',b,L] using hA)
    (by simpa only [show b+8*q-q=b+7*q by omega] using hb₁)
    (by simpa only [sub_self] using hroot)
    (by simpa only [sub_self,show t+8*q-q=7*q+t by omega] using hB)
  omega
