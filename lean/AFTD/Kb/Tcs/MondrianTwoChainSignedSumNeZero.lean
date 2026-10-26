import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianTwoChainPrefixBound
import AFTD.Kb.Tcs.MondrianTwoChainLowerSumLt
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_two_chain_signed_sum_ne_zero

Topic: combinatorics   Node: f808386b0b23

Provenance: helper lemma. For the three-prime extension of OP-280, arXiv:2610.19193, Section 1. This develops the proved mondrian_no_perfect_two_prime_area and the width-free signed-height relation from this session.

A nonempty signed sum of distinct numbers drawn from the chains C*p^a and C*r*p^a cannot vanish when C is positive, r≥2 and p>r+1.
-/

theorem mondrian_two_chain_signed_sum_ne_zero (p r C : ℕ)
    (hC : 0 < C) (hr : 2 ≤ r) (hpr : r + 1 < p)
    (L : List (ℕ × Bool)) (hne : L ≠ []) (hnd : (L.map Prod.fst).Nodup)
    (hrep : ∀ t ∈ L, ∃ a : ℕ, t.1 = C * p ^ a ∨ t.1 = C * r * p ^ a) :
    (L.map (fun t => if t.2 then (t.1 : ℤ) else -(t.1 : ℤ))).sum ≠ 0 := by
  classical
  let T := L.toFinset
  let g := fun t : ℕ × Bool => if t.2 then (t.1 : ℤ) else -(t.1 : ℤ)
  have hT : T.Nonempty := by
    cases L with
    | nil => simp at hne
    | cons t L => exact ⟨t, by simp [T]⟩
  have hLnd : L.Nodup := List.Nodup.of_map Prod.fst hnd
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x.1 = y.1 → x = y := by
    intro x hx y hy hxy
    exact List.inj_on_of_nodup_map hnd (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy
  obtain ⟨t, ht, hmax⟩ := T.exists_max_image Prod.fst hT
  let R := T.erase t
  let V := R.image Prod.fst
  have hV : ∀ y ∈ V, ∃ a, y = C * p ^ a ∨ y = C * r * p ^ a := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    exact hrep u (List.mem_toFinset.mp (Finset.mem_erase.mp hu).2)
  have hVlt : ∀ y ∈ V, y < t.1 := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have huT := (Finset.mem_erase.mp hu).2
    have hune := (Finset.mem_erase.mp hu).1
    have hle := hmax u huT
    have hneq : u.1 ≠ t.1 := fun he => hune (hinj u huT t ht he)
    omega
  have hsumV : V.sum id = R.sum Prod.fst := by
    apply Finset.sum_image
    intro x hx y hy he
    exact hinj x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2 he
  have hpref := mondrian_two_chain_lower_sum_lt p r C t.1 hC hr hpr
    (hrep t (List.mem_toFinset.mp ht)) V hV hVlt
  rw [hsumV] at hpref
  have hprefZ : ((R.sum Prod.fst : ℕ) : ℤ) < (t.1 : ℤ) := by exact_mod_cast hpref
  have hbound : ∀ u : ℕ × Bool, g u ≤ (u.1 : ℤ) ∧ -g u ≤ (u.1 : ℤ) := by
    rintro ⟨a, b⟩
    cases b <;> simp [g] <;> omega
  have hpos : R.sum g ≤ ((R.sum Prod.fst : ℕ) : ℤ) := by
    have hh := Finset.sum_le_sum (fun u (hu : u ∈ R) => (hbound u).1)
    simpa only [Nat.cast_sum] using hh
  have hneg : -(R.sum g) ≤ ((R.sum Prod.fst : ℕ) : ℤ) := by
    have hh := Finset.sum_le_sum (fun u (hu : u ∈ R) => (hbound u).2)
    simpa only [Finset.sum_neg_distrib, Nat.cast_sum] using hh
  intro hzero
  have hsum0 : T.sum g = 0 := by
    rw [List.sum_toFinset g hLnd]
    exact hzero
  have he : g t + R.sum g = 0 := by
    change g t + (T.erase t).sum g = 0
    rw [Finset.add_sum_erase T g ht, hsum0]
  have hgt : g t = if t.2 then (t.1 : ℤ) else -(t.1 : ℤ) := rfl
  rw [hgt] at he
  cases hb : t.2 <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at he <;> linarith
