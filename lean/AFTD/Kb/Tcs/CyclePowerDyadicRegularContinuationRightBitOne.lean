import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_dyadic_regular_continuation_right_bit_one

Topic: combinatorics   Node: d8d90ab0ca5e

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there). Partial result towards the stated cycle_power_dyadic_regular_continuation_right: its conclusion restricted to offset 1 of the two new classes.

First part of the rightward continuation, for every exponent t+1 ≥ 3, without the coverage hypothesis. In a tight, exactly dyadically covered integer Boolean class model at exponent t+1 with exactly t+2 active classes at every vertex, suppose that for every root r with p0 - 3·2^t ≤ r ≤ p0: if p0 - r is even, the class rooted at r contains offset 1 and its offsets come in consecutive pairs (2i and 2i+1 both in or both out, i < 2^t); if p0 - r is odd, that class consists of its two endpoints only. Then the class rooted at p0+1 does not contain offset 1 and the class rooted at p0+2 does: bit 1 keeps alternating for two more roots.
-/

theorem cycle_power_dyadic_regular_continuation_right_bit_one (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (p0 : ℤ)
    (hreg : ∀ r : ℤ, p0 - 3*2^t ≤ r → r ≤ p0 →
      ((p0 - r) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
      ((p0 - r) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) :
    x (p0+1) 1 = false ∧ x (p0+2) 1 = true := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2^t := ⟨_, rfl⟩
  have hT4 : 4 ≤ T := by
    rw [hT]
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^t := Nat.pow_le_pow_right (by norm_num) ht
  have hD : (2:ℕ)^(t+1) = 2*T := by rw [hT, pow_succ]; ring
  have hTz : ((2:ℤ))^t = (T:ℤ) := by rw [hT]; push_cast; rfl
  have hx : ∀ (q q' : ℤ) (a a' : ℕ), q = q' → a = a' → x q a = x q' a' := by
    intro q q' a a' h1 h2; rw [h1, h2]
  have hends : ∀ v : ℤ, x v 0 = true ∧ x v (2^(t+1) - 1) = true := by
    intro v
    have h := hexact 0 (by omega) v
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
      Nat.zero_add] at h
    revert h
    generalize x v 0 = u
    generalize x v (2^(t+1) - 1) = w
    cases u <;> cases w <;> simp
  have hk1 : x p0 1 = true := ((hreg p0 (by rw [hTz]; omega) le_rfl).1 (by simp)).1
  -- rank one exactness at p0+1: the class at p0 owns the pair, so the class at p0+1 lacks offset D-2
  have hD2 : x (p0+1) (2^(t+1) - 2) = false := by
    have h := hexact 1 (by omega) (p0+1)
    rw [show (2:ℕ)^1 = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at h
    rw [hx (p0+1-((0:ℕ):ℤ)) (p0+1) 0 0 (by simp) rfl,
      hx (p0+1-((0:ℕ):ℤ)) (p0+1) (0+2^(t+1)-(1+1)) (2^(t+1)-2) (by simp) (by omega),
      hx (p0+1-((1:ℕ):ℤ)) p0 1 1 (by push_cast; ring) rfl,
      hx (p0+1-((1:ℕ):ℤ)) p0 (1+2^(t+1)-(1+1)) (2^(t+1)-1) (by push_cast; ring) (by omega),
      hk1, (hends p0).2, (hends (p0+1)).1] at h
    revert h
    generalize x (p0+1) (2^(t+1) - 2) = w
    cases w <;> simp
  have hb2 : x (p0+1) 2 = false := by
    by_contra hne
    have h2 : x (p0+1) 2 = true := by
      revert hne; generalize x (p0+1) 2 = w; cases w <;> simp
    have hp := (cycle_power_dyadic_tight_class_parent (t+1) 2 (by norm_num) (by omega) (x (p0+1))
      (htight (p0+1)) 2 (by norm_num)).2 (by norm_num) h2
    rw [hx (p0+1) (p0+1) (2 + 2^(t+1) - 2^2) (2^(t+1) - 2) rfl (by norm_num; omega), hD2] at hp
    exact absurd hp (by decide)
  -- compare the counts at p0+2 and p0+3
  obtain ⟨E, hE⟩ : ∃ E : ℕ, 2^(t+1) = E + 3 := ⟨2^(t+1) - 3, by omega⟩
  have split2 : ∀ f : ℕ → ℕ, (Finset.range (E+3)).sum f =
      f 0 + f 1 + (Finset.range E).sum (fun a => f (a+2)) + f (E+2) := by
    intro f
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  have split3 : ∀ f : ℕ → ℕ, (Finset.range (E+3)).sum f =
      f 0 + f 1 + f 2 + (Finset.range E).sum (fun a => f (a+3)) := by
    intro f
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  have h2 := hcount (p0+2)
  have h3 := hcount (p0+3)
  rw [hE, split2] at h2
  rw [hE, split3] at h3
  have hmid : (Finset.range E).sum (fun a => (x (p0+2-((a+2 : ℕ) : ℤ)) (a+2)).toNat) =
      (Finset.range E).sum (fun a => (x (p0+3-((a+3 : ℕ) : ℤ)) (a+3)).toNat) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have haE := Finset.mem_range.mp ha
    have hr := hreg (p0 - (a:ℤ)) (by rw [hTz]; omega) (by omega)
    rw [hx (p0+2-((a+2 : ℕ) : ℤ)) (p0 - (a:ℤ)) (a+2) (a+2) (by push_cast; ring) rfl,
      hx (p0+3-((a+3 : ℕ) : ℤ)) (p0 - (a:ℤ)) (a+3) (a+3) (by push_cast; ring) rfl]
    rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar
    · have hp := (hr.1 (by omega)).2 (a/2+1) (by rw [← hT]; omega)
      rw [hx _ _ (a+2) (2*(a/2+1)) rfl (by omega), hp]
      exact congrArg Bool.toNat (hx _ _ _ _ rfl (by omega))
    · rw [hr.2 (by omega) (a+2) (by omega) (by omega), hr.2 (by omega) (a+3) (by omega) (by omega)]
  have f0 : (x (p0+2-((0:ℕ):ℤ)) 0).toNat = 1 := by
    rw [hx _ (p0+2) 0 0 (by simp) rfl, (hends _).1]; rfl
  have f1 : (x (p0+2-((1:ℕ):ℤ)) 1).toNat = (x (p0+1) 1).toNat := by
    rw [hx _ (p0+1) 1 1 (by push_cast; ring) rfl]
  have fE : (x (p0+2-((E+2:ℕ):ℤ)) (E+2)).toNat = 1 := by
    rw [hx _ (p0+2-((E+2:ℕ):ℤ)) (E+2) (2^(t+1) - 1) rfl (by omega), (hends _).2]; rfl
  have g0 : (x (p0+3-((0:ℕ):ℤ)) 0).toNat = 1 := by
    rw [hx _ (p0+3) 0 0 (by simp) rfl, (hends _).1]; rfl
  have g1 : (x (p0+3-((1:ℕ):ℤ)) 1).toNat = (x (p0+2) 1).toNat := by
    rw [hx _ (p0+2) 1 1 (by push_cast; ring) rfl]
  have g2 : (x (p0+3-((2:ℕ):ℤ)) 2).toNat = 0 := by
    rw [hx _ (p0+1) 2 2 (by push_cast; ring) rfl, hb2]; rfl
  rw [f0, f1, fE, hmid] at h2
  rw [g0, g1, g2] at h3
  have hfin : (x (p0+1) 1).toNat + 1 = (x (p0+2) 1).toNat := by omega
  revert hfin
  generalize x (p0+1) 1 = u
  generalize x (p0+2) 1 = w
  cases u <;> cases w <;> simp
