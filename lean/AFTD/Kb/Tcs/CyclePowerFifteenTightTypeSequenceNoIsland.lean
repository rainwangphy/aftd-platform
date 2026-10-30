import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceShapeRulesCore
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteen
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceTwoIffThree

/-!
# cycle_power_fifteen_tight_type_sequence_no_island

Topic: combinatorics   Node: 9efd46ea5afb

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

No islands for k = 15: in the layer-free tight-class model of bandwidth fifteen on the integer line (the interface of the one_iff_fourteen lemma), every class is an initial interval of offsets together with a terminal interval: if a < b < c < 16, the class at p misses p + a and contains p + b, then it contains p + c.
-/

set_option maxHeartbeats 4000000 in
theorem cycle_power_fifteen_tight_type_sequence_no_island_aux
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
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 16 →
      x p a = false → x p b = true → x p c = true := by
  have h114 := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen x h0 h15 hparent hcount hexact hcover
  have h23 := cycle_power_fifteen_tight_type_sequence_two_iff_three x h0 h15 hparent hcount hexact hcover
  intro p
  have hsh : ∀ u a : ℤ, u - a + p = u + p - a := fun u a => by ring
  have hpar : ∀ q : ℤ, ∀ i j : ℕ, (i, j) ∈ ({(1,15),(2,14),(3,15),(4,12),(5,13),(6,14),(7,15),
      (8,0),(9,1),(10,2),(11,3),(12,0),(13,1),(14,0)} : Finset (ℕ × ℕ)) →
      x q i = true → x q j = true := fun q i j h => hparent q (i, j) h
  have key := cycle_power_fifteen_tight_type_sequence_shape_rules_core (fun q (j : Fin 16) => x (q + p) (j : ℕ))
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
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 2 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 3 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 4 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 5 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 6 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 7 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 9 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 10 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 11 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (by
      intro u
      obtain ⟨a, ha, h1, h2⟩ := hcover 13 (by norm_num) (by norm_num) (u + p)
      simp only [hsh]
      clear hcount hexact hcover hparent hpar h114 h23
      interval_cases a <;> simp_all <;> omega)
    (fun q h => hpar (q + p) 2 14 (by decide) h)
    (fun q h => hpar (q + p) 4 12 (by decide) h)
    (fun q h => hpar (q + p) 5 13 (by decide) h)
    (fun q h => hpar (q + p) 6 14 (by decide) h)
    (fun q h => hpar (q + p) 9 1 (by decide) h)
    (fun q h => hpar (q + p) 10 2 (by decide) h)
    (fun q h => hpar (q + p) 11 3 (by decide) h)
    (fun q h => hpar (q + p) 13 1 (by decide) h)
    (fun q => h114 (q + p))
    (fun q => h23 (q + p))
  simp only [zero_add] at key
  obtain ⟨r4_3, r5_4, r6_5, r7_6, r8_9, r9_10, r10_11, r11_12, r12_13⟩ := key
  have M1 : ∀ i, i < 7 → x p (i + 1) = true → x p i = true := by
    intro i hi h
    interval_cases i
    · exact h0 p
    · rw [h114 p]; exact hpar p 2 14 (by decide) h
    · rw [h23 p]; exact h
    · exact r4_3 h
    · exact r5_4 h
    · exact r6_5 h
    · exact r7_6 h
  have M2 : ∀ i, 8 ≤ i → i < 15 → x p i = true → x p (i + 1) = true := by
    intro i hi hi' h
    interval_cases i
    · exact r8_9 h
    · exact r9_10 h
    · exact r10_11 h
    · exact r11_12 h
    · exact r12_13 h
    · rw [← h114 p]; exact hpar p 13 1 (by decide) h
    · exact h15 p
  have P1 : ∀ j, j ≤ 7 → x p j = true → ∀ i, i ≤ j → x p i = true := by
    intro j
    induction j with
    | zero =>
      intro _ h i hi
      have hi0 : i = 0 := by omega
      subst hi0; exact h
    | succ j ih =>
      intro hj h i hi
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact ih (by omega) (M1 j (by omega) h) i (by omega)
      · have hij : i = j + 1 := by omega
        subst hij; exact h
  have P2 : ∀ c b, 8 ≤ b → b ≤ c → c < 16 → x p b = true → x p c = true := by
    intro c
    induction c with
    | zero => intro b hb hbc; omega
    | succ c ih =>
      intro b hb hbc hc h
      rcases Nat.lt_or_ge b (c + 1) with hlt | hge
      · exact M2 c (by omega) (by omega) (ih b hb (by omega) (by omega) h)
      · have hbc' : b = c + 1 := by omega
        subst hbc'; exact h
  intro a b c hab hbc hc ha hb
  rcases Nat.lt_or_ge b 8 with h8 | h8
  · have hxa := P1 b (by omega) hb a (by omega)
    rw [hxa] at ha; exact absurd ha (by decide)
  · exact P2 c b h8 (by omega) hc hb

theorem cycle_power_fifteen_tight_type_sequence_no_island
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
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 16 →
      x p a = false → x p b = true → x p c = true := cycle_power_fifteen_tight_type_sequence_no_island_aux x h0 h15 hparent hcount hexact hcover
