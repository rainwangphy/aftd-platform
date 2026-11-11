import AFTD.Prelude

/-!
# cycle_power_four_corrected_count_periodic_of_count

Topic: combinatorics   Node: ad99afeb80b8

Provenance: helper lemma. Corrected lower-count periodicity in the zero-phase defective half-model for RT-1 and OP-205.

At span four, endpoint membership, the defective top-owner equation, and the defective active-count equation alone force the lower-half count plus the defect to be two-periodic.
-/

theorem cycle_power_four_corrected_count_periodic_of_count
    (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hend : ∀ p, y p 0 = true ∧ y p 3 = true)
    (htop : ∀ v : ℤ, (Finset.range 2).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+2)).toNat) + (e v).toNat = 1)
    (hcount : ∀ v : ℤ, (Finset.range 4).sum (fun a =>
      (y (v-(a:ℤ)) a).toNat) + (e v).toNat = 3) :
    ∀ v : ℤ,
      (Finset.range 2).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat =
      (Finset.range 2).sum (fun a => (y (v+2-(a:ℤ)) a).toNat) + (e (v+2)).toNat := by
  intro v
  have ht := htop v
  have hc2 := hcount (v+2)
  norm_num [Finset.sum_range_succ, hend] at ht hc2 ⊢
  omega
