import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_eight_block_boundary_owner_transfer

Topic: combinatorics   Node: aebadc6e5738

Provenance: helper lemma. Uniform local structural route for OP-205 / RT-1, following arXiv:2610.15635. The Boolean eight-block extension remains conjectured; the induction result keeps it as an explicit hypothesis. Finite guarded computations are evidence only, and no graph covering value or research advance is claimed.

Let 0<L<q. Assume first eighths are prefixes, the6q parent implications hold, and6q/7q edges have exact owners. If root0 selects0 andq but missesL and edge(L,7q) is covered, some t<L gives root L-q-t selecting q+t and7q+t but missing q+t-L. The new gap between selected and missing compressed positions equals q-L.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_boundary_owner_transfer
    (q L : ℕ) (hq : 0 < q) (hL₀ : 0 < L) (hLq : L < q)
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
    (hroot : x 0 0 = true) (hchild : x 0 q = true)
    (hmiss : x 0 L = false)
    (hcover : ∃ a : ℕ, a < q+L ∧ x ((L : ℤ)-(a : ℤ)) a = true ∧
      x ((L : ℤ)-(a : ℤ)) (a+7*q-L) = true) :
    ∃ t : ℕ, t < L ∧
      x ((L : ℤ)-(q : ℤ)-(t : ℤ)) (q+t) = true ∧
      x ((L : ℤ)-(q : ℤ)-(t : ℤ)) (7*q+t) = true ∧
      x ((L : ℤ)-(q : ℤ)-(t : ℤ)) (q+t-L) = false := by
  have hB : x 0 (7*q) = true := by
    have h := (hparent 0 q (by omega)).2 (by omega) hchild
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
      have hp : (q : ℤ)-(b : ℤ)=(L : ℤ)-(a : ℤ) := by dsimp [b]; omega
      have hi : b+6*q=a+7*q-L := by dsimp [b]; omega
      have hb₁ : x ((q : ℤ)-(b : ℤ)) (b+6*q) = true := by
        simpa only [hp,hi] using ha₁
      have hb₀ := (hparent ((q : ℤ)-(b : ℤ)) b (by omega)).1 hbq hb₁
      have huniq := cycle_power_exact_pair_unique (8*q) (2*q) x h6'
        (q : ℤ) b q (by omega) (by omega) hb₀
        (by convert hb₁ using 1 <;> congr 1 <;> omega)
        (by simpa only [sub_self] using hchild)
        (by simpa only [sub_self,show q+8*q-2*q=7*q by omega] using hB)
      omega
    · let b := a-L
      have hbq : b < q := by dsimp [b]; omega
      have hp : -(b : ℤ)=(L : ℤ)-(a : ℤ) := by dsimp [b]; omega
      have hb₀ : x (-(b : ℤ)) b = true := by
        have h := hprefix ((L : ℤ)-(a : ℤ)) b a (by dsimp [b]; omega) haq ha₀
        simpa only [hp] using h
      have hb₁ : x (-(b : ℤ)) (b+7*q) = true := by
        have hi : b+7*q=a+7*q-L := by dsimp [b]; omega
        simpa only [hp,hi] using ha₁
      have huniq := cycle_power_exact_pair_unique (8*q) q x h7'
        (0 : ℤ) b 0 hbq hq
        (by simpa only [zero_sub] using hb₀)
        (by simpa only [zero_sub,show b+8*q-q=b+7*q by omega] using hb₁)
        (by simpa using hroot)
        (by simpa only [Nat.cast_zero,sub_zero,zero_add,show 8*q-q=7*q by omega] using hB)
      have haeq : a=L := by dsimp [b] at huniq; omega
      subst a
      have hlow : x 0 L = true := by simpa only [sub_self] using ha₀
      rw [hmiss] at hlow
      contradiction
  let t := a-q
  have ht : t < L := by dsimp [t]; omega
  have haeq : a=q+t := by dsimp [t]; omega
  have hp : (L : ℤ)-(a : ℤ)=(L : ℤ)-(q : ℤ)-(t : ℤ) := by omega
  have hC : x ((L : ℤ)-(q : ℤ)-(t : ℤ)) (q+t) = true := by
    simpa only [← haeq,← hp] using ha₀
  have hB' : x ((L : ℤ)-(q : ℤ)-(t : ℤ)) (7*q+t) = true := by
    have h := (hparent ((L : ℤ)-(q : ℤ)-(t : ℤ)) (q+t) (by omega)).2
      (by omega) hC
    convert h using 1 <;> congr 1 <;> omega
  refine ⟨t, ht, hC, hB', ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hA
  let b := q+t-L
  have hb₀ : 0 < b := by dsimp [b]; omega
  have hbq : b < q := by dsimp [b]; omega
  have hp' : -(b : ℤ)=(L : ℤ)-(q : ℤ)-(t : ℤ) := by dsimp [b]; omega
  have hb₁ : x (-(b : ℤ)) (b+7*q) = true := by
    have hi : b+7*q=a+7*q-L := by dsimp [b]; omega
    simpa only [hp',hi,← hp] using ha₁
  have huniq := cycle_power_exact_pair_unique (8*q) q x h7'
    (0 : ℤ) b 0 hbq hq
    (by simpa only [zero_sub,hp',b] using hA)
    (by simpa only [zero_sub,show b+8*q-q=b+7*q by omega] using hb₁)
    (by simpa using hroot)
    (by simpa only [Nat.cast_zero,sub_zero,zero_add,show 8*q-q=7*q by omega] using hB)
  omega
