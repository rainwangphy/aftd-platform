import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandCorner

/-!
# cycle_power_dyadic_endpoint_overlap_of_no_island

Topic: combinatorics   Node: 844111ace3ea

Provenance: helper lemma. Conjectured uniform helper for OP-205 / RT-1, following arXiv:2610.15635. Experiments6472 and6481 suggest a split into global periodic two-interval classification and local endpoint geometry, allowing arbitrary unequal interval widths. The statements are unproved; finite SAT evidence is not a uniform theorem. No advance is claimed.

Conjectured local uniform geometry: if all tight dyadic classes are unions of an initial and terminal interval, with arbitrary unequal widths, exact dyadic edges and full ordinary coverage force endpoint overlap. No periodicity or optimal scalar-count assumption is required.
-/

open Finset

theorem cycle_power_dyadic_endpoint_overlap_of_no_island
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (Finset.range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2 ^ m - d ∧ x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true)
    (hshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2 ^ m →
      x p a = false → x p b = true → x p c = true) :
    ∀ (p : ℤ) (q : ℕ), 1 ≤ q → q < 2 ^ m →
      x (p + (q : ℤ)) (2 ^ m - 1 - q) = true →
      ∃ a : ℕ, a < q ∧ x (p + (q : ℤ)) (2 ^ m - q + a) = true ∧
        x (p + ((2 ^ m : ℕ) : ℤ)) a = true := by
  have hroot (p : ℤ) : x p 0 = true ∧ x p (2^m-1) = true := by
    have hh := hexact 0 (by omega) p
    norm_num only [pow_zero,sum_range_one,Nat.cast_zero,sub_zero,Nat.zero_add] at hh
    cases h0 : x p 0 <;> cases h1 : x p (2^m-1) <;> simp_all
  intro p q hq0 hq1 hmem
  have hprev : x (p+(q : ℤ)) (2^m-q-1) = true := by
    convert hmem using 1 <;> congr 1 <;> omega
  have hc := cycle_power_dyadic_no_island_corner m x htight hexact hshape hcover
    (p+(q : ℤ)) (2^m-q) (by omega) (by omega) hprev
  rcases hc with hc | hc
  · refine ⟨0,by omega,?_,(hroot _).1⟩
    simpa only [Nat.add_zero] using hc
  · refine ⟨q-1,by omega,?_,?_⟩
    · have he : 2^m-q+(q-1)=2^m-1 := by omega
      rw [he]
      exact (hroot _).2
    · have hr : p+(q : ℤ)+((2^m-q : ℕ) : ℤ)=p+((2^m : ℕ) : ℤ) := by omega
      have hi : 2^m-(2^m-q)-1=q-1 := by omega
      rwa [hr,hi] at hc
