import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_fifteen_model_no_island

Topic: combinatorics   Node: d1b449e0c1bb

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

The no-island class shape at exponent m = 4 (bandwidth 15), in the exact form the conditional theorem simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape assumes: every tight, exactly dyadically covered, fully ordinarily covered integer Boolean class model with exactly five active classes at each vertex has classes that are an initial interval together with a terminal interval.
-/

theorem cycle_power_fifteen_model_no_island (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight 4 (x p) =
      (Finset.range (2^4)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^4-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^4 → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^4-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^4)).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = 4+1) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^4 →
      x p a = false → x p b = true → x p c = true := by
  have hends : ∀ v : ℤ, x v 0 = true ∧ x v 15 = true := by
    intro v
    have h := hexact 0 (by norm_num) v
    simp at h
    exact h
  have h0 : ∀ p, x p 0 = true := fun p => (hends p).1
  have h15 : ∀ p, x p 15 = true := fun p => (hends p).2
  have hparent : ∀ p : ℤ, ∀ e ∈ ({(1,15),(2,14),(3,15),(4,12),(5,13),(6,14),(7,15),
      (8,0),(9,1),(10,2),(11,3),(12,0),(13,1),(14,0)} : Finset (ℕ × ℕ)),
      x p e.1 = true → x p e.2 = true := by
    intro p e he h
    have P2 := cycle_power_dyadic_tight_class_parent 4 2 (by norm_num) (by norm_num) (x p) (htight p)
    have P3 := cycle_power_dyadic_tight_class_parent 4 3 (by norm_num) (by norm_num) (x p) (htight p)
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h15 p
    · exact (P2 2 (by norm_num)).2 (by norm_num) h
    · exact h15 p
    · exact (P3 4 (by norm_num)).2 (by norm_num) h
    · exact (P3 5 (by norm_num)).2 (by norm_num) h
    · exact (P3 6 (by norm_num)).2 (by norm_num) h
    · exact h15 p
    · exact h0 p
    · exact (P3 1 (by norm_num)).1 (by norm_num) h
    · exact (P3 2 (by norm_num)).1 (by norm_num) h
    · exact (P3 3 (by norm_num)).1 (by norm_num) h
    · exact h0 p
    · exact (P2 1 (by norm_num)).1 (by norm_num) h
    · exact h0 p
  have hcount' : ∀ v : ℤ, (Finset.range 14).sum
      (fun j => (x (v - ((j + 1 : ℕ) : ℤ)) (j + 1)).toNat) = 3 := by
    intro v
    have h := hcount v
    rw [show (2:ℕ)^4 = 14 + 1 + 1 by norm_num, Finset.sum_range_succ, Finset.sum_range_succ'] at h
    have e0 : (x (v - ((0 : ℕ) : ℤ)) 0).toNat = 1 := by rw [h0]; rfl
    have e15 : (x (v - ((14 + 1 : ℕ) : ℤ)) (14 + 1)).toNat = 1 := by rw [h15]; rfl
    omega
  have hexact' : ∀ d ∈ ({8,12,14} : Finset ℕ), ∀ v : ℤ,
      (Finset.range (16 - d)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + d)).toNat) = 1 := by
    intro d hd v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · rw [show 16 - 8 = 2^3 by norm_num]
      refine Eq.trans (Finset.sum_congr rfl ?_) (hexact 3 (by norm_num) v)
      intro a _
      rw [show a + 2^4 - 2^3 = a + 8 by simp only [Nat.reducePow]; omega]
    · rw [show 16 - 12 = 2^2 by norm_num]
      refine Eq.trans (Finset.sum_congr rfl ?_) (hexact 2 (by norm_num) v)
      intro a _
      rw [show a + 2^4 - 2^2 = a + 12 by simp only [Nat.reducePow]; omega]
    · rw [show 16 - 14 = 2^1 by norm_num]
      refine Eq.trans (Finset.sum_congr rfl ?_) (hexact 1 (by norm_num) v)
      intro a _
      rw [show a + 2^4 - 2^1 = a + 14 by simp only [Nat.reducePow]; omega]
  have hcover' : ∀ (d : ℕ), 1 ≤ d → d < 15 → ∀ v : ℤ,
      ∃ a < 16 - d, x (v - (a : ℤ)) a = true ∧ x (v - (a : ℤ)) (a + d) = true := by
    intro d hd1 hd v
    obtain ⟨a, ha, h1, h2⟩ := hcover d hd1 (by simp only [Nat.reducePow]; omega) v
    exact ⟨a, by simp only [Nat.reducePow] at ha; omega, h1, h2⟩
  intro p a b c hab hbc hc
  exact cycle_power_fifteen_tight_type_sequence_no_island x h0 h15 hparent hcount' hexact' hcover'
    p a b c hab hbc (by simpa using hc)
