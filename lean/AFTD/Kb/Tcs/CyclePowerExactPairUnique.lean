import AFTD.Prelude

/-!
# cycle_power_exact_pair_unique

Topic: combinatorics   Node: c6f3d95b5a2e

Provenance: helper lemma. Conditional structural helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The no-island hypothesis remains explicit and unproved for the general periodic model. These helpers do not settle the covering-number conjecture, and no research advance is claimed.

An exact Boolean long-edge count of one gives a unique owning rooted class.
-/

open Finset

theorem cycle_power_exact_pair_unique
    (D R : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) = 1)
    (v : ℤ) (a b : ℕ) (ha : a < R) (hb : b < R)
    (ha0 : x (v-(a : ℤ)) a = true)
    (ha1 : x (v-(a : ℤ)) (a+D-R) = true)
    (hb0 : x (v-(b : ℤ)) b = true)
    (hb1 : x (v-(b : ℤ)) (b+D-R) = true) :
    a = b := by
  classical
  by_contra hne
  let f : ℕ → ℕ := fun c =>
    (x (v-(c : ℤ)) c && x (v-(c : ℤ)) (c+D-R)).toNat
  have hsub : ({a,b} : Finset ℕ) ⊆ range R := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact mem_range.mpr ha
    · exact mem_range.mpr hb
  have hle : ({a,b} : Finset ℕ).sum f ≤ (range R).sum f :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hsmall : ({a,b} : Finset ℕ).sum f = 2 := by
    simp [f, hne, ha0, ha1, hb0, hb1]
  rw [hsmall, show (range R).sum f = 1 from hexact v] at hle
  omega
