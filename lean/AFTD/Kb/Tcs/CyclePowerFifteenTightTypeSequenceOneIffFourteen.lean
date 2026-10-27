import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCore

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen

Topic: combinatorics   Node: 1e7bfae6c1f6

Provenance: helper lemma. Semantic bridge for the k=15 classification bottleneck of OP-205, arXiv:2610.15635 Section 3, RT-1. This is the analogue of the proved bandwidth-seven pure type-sequence lemma.

In the layer-free tight-class model for bandwidth fifteen, the first inner position belongs to a class exactly when the penultimate position does.
-/

set_option maxHeartbeats 4000000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_aux
    (x : ℤ → ℕ → Bool) (h0 : ∀ p, x p 0 = true) (h15 : ∀ p, x p 15 = true)
    (hparent : ∀ p : ℤ, ∀ e ∈ ({(1,15),(2,14),(3,15),(4,12),(5,13),(6,14),(7,15),
      (8,0),(9,1),(10,2),(11,3),(12,0),(13,1),(14,0)} : Finset (ℕ × ℕ)),
      x p e.1 = true → x p e.2 = true)
    (hcount : ∀ v : ℤ, (Finset.range 14).sum
      (fun j => (x (v - ((j + 1 : ℕ) : ℤ)) (j + 1)).toNat) = 3)
    (hexact : ∀ d ∈ ({8,12,14} : Finset ℕ), ∀ v : ℤ,
      (Finset.range (16 - d)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + d)).toNat) = 1)
    (hcover : ∀ (d : ℕ), 1 ≤ d → d < 15 → ∀ v : ℤ,
      ∃ a < 16 - d, x (v - (a : ℤ)) a = true ∧ x (v - (a : ℤ)) (a + d) = true) :
    ∀ p, x p 1 = x p 14 := by
  intro p
  have hsh : ∀ u a : ℤ, u - a + p = u + p - a := fun u a => by ring
  have hpar : ∀ q : ℤ, ∀ i j : ℕ, (i, j) ∈ ({(1,15),(2,14),(3,15),(4,12),(5,13),(6,14),(7,15),
      (8,0),(9,1),(10,2),(11,3),(12,0),(13,1),(14,0)} : Finset (ℕ × ℕ)) →
      x q i = true → x q j = true := fun q i j h => hparent q (i, j) h
  have key := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core (fun q (j : Fin 16) => x (q + p) (j : ℕ))
    (by
      intro u
      have h := hcount (u + p)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      simp only [hsh]
      simpa using h)
    (by
      intro u
      have h := hexact 14 (by simp) (u + p)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      simp only [hsh]
      simpa [h0, h15] using h)
    (by
      intro u
      have h := hexact 12 (by simp) (u + p)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      simp only [hsh]
      simpa [h0, h15] using h)
    (by
      intro u
      have h := hexact 8 (by simp) (u + p)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      simp only [hsh]
      simpa [h0, h15] using h)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 1 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 2 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 3 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 4 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 5 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 6 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 7 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 9 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 10 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 11 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 13 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar
      interval_cases a <;> simp_all <;> omega)
    (fun q h => hpar (q + p) 2 14 (by decide) h)
    (fun q h => hpar (q + p) 4 12 (by decide) h)
    (fun q h => hpar (q + p) 5 13 (by decide) h)
    (fun q h => hpar (q + p) 6 14 (by decide) h)
    (fun q h => hpar (q + p) 9 1 (by decide) h)
    (fun q h => hpar (q + p) 10 2 (by decide) h)
    (fun q h => hpar (q + p) 11 3 (by decide) h)
    (fun q h => hpar (q + p) 13 1 (by decide) h)
  simpa using key

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen
    (x : ℤ → ℕ → Bool) (h0 : ∀ p, x p 0 = true) (h15 : ∀ p, x p 15 = true)
    (hparent : ∀ p : ℤ, ∀ e ∈ ({(1,15),(2,14),(3,15),(4,12),(5,13),(6,14),(7,15),
      (8,0),(9,1),(10,2),(11,3),(12,0),(13,1),(14,0)} : Finset (ℕ × ℕ)),
      x p e.1 = true → x p e.2 = true)
    (hcount : ∀ v : ℤ, (Finset.range 14).sum
      (fun j => (x (v - ((j + 1 : ℕ) : ℤ)) (j + 1)).toNat) = 3)
    (hexact : ∀ d ∈ ({8,12,14} : Finset ℕ), ∀ v : ℤ,
      (Finset.range (16 - d)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + d)).toNat) = 1)
    (hcover : ∀ (d : ℕ), 1 ≤ d → d < 15 → ∀ v : ℤ,
      ∃ a < 16 - d, x (v - (a : ℤ)) a = true ∧ x (v - (a : ℤ)) (a + d) = true) :
    ∀ p, x p 1 = x p 14 := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_aux x h0 h15 hparent hcount hexact hcover
