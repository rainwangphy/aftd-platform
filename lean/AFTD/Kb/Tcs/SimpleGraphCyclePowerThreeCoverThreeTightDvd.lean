import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.FinThreeNotForallEqOrEq
import AFTD.Kb.Tcs.FinThreeEqOfFiveNe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeAdjIff
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.FinThreeFalseOfFourPairwiseNe

/-!
# simple_graph_cycle_power_three_cover_three_tight_dvd

Topic: combinatorics   Node: d0db3867fd8d

Provenance: helper lemma. Step toward simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd (the k = 3 case of OP-205, arXiv:2610.15635): the double-counting proof found in thread RT-1.

If three labellings with clique classes satisfy the tight structure (each distance-3 pair and each distance-2 pair in exactly one layer, every class spanned by a distance-3 pair), then 4 divides n.
-/

theorem simple_graph_cycle_power_three_cover_three_tight_dvd (n : ℕ) [NeZero n] (hn : 10 ≤ n)
    (c : Fin 3 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 3).Adj u v)
    (h3 : ∀ i, ∃! s, c s i = c s (i + 3)) (h2 : ∀ i, ∃! s, c s i = c s (i + 2))
    (hspan : ∀ s i, ∃ d : ℕ, d ≤ 3 ∧ c s (i - d) = c s (i - d + 3) ∧ c s (i - d) = c s i) :
    4 ∣ n := by
  have fin3_four := fin_three_false_of_four_pairwise_ne
  have fin3_two := fin_three_not_forall_eq_or_eq
  have fin3_five := fin_three_eq_of_five_ne
  classical
  -- integers as positions
  have cinj : ∀ a b : ℤ, |a - b| < n → (((a : ℤ) : ZMod n) = ((b : ℤ) : ZMod n) ↔ a = b) :=
    fun a b h => zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b h
  have hn' : (10 : ℤ) ≤ n := by exact_mod_cast hn
  -- members of a class are within offset 3
  have hmem : ∀ s (k : ℤ) (z : ZMod n), c s (k : ZMod n) = c s z →
      ∃ e : ℤ, |e| ≤ 3 ∧ z = ((k + e : ℤ) : ZMod n) := by
    intro s k z h
    by_cases hz : (k : ZMod n) = z
    · exact ⟨0, by simp, by simp [hz]⟩
    · obtain ⟨e, -, he, rfl⟩ := (simple_graph_cycle_power_three_adj_iff n hn _ _).mp (hc s _ _ hz h)
      exact ⟨e, he, by push_cast; ring⟩
  -- two positions in one class differ by at most 3
  have hnear : ∀ s (k e : ℤ), |e| ≤ 6 → c s (k : ZMod n) = c s ((k + e : ℤ) : ZMod n) → |e| ≤ 3 := by
    intro s k e he h
    obtain ⟨e', he', hz⟩ := hmem s k _ h
    have := (cinj (k + e) (k + e') (by
      rw [show k + e - (k + e') = e - e' by ring, abs_lt]
      rw [abs_le] at he he'; constructor <;> omega)).mp hz
    rw [abs_le] at he' ⊢; omega
  -- the window of k in its layer
  set lam : ZMod n → Fin 3 := fun i => (h3 i).exists.choose with hlamdef
  have hlam : ∀ i, c (lam i) i = c (lam i) (i + 3) := fun i => (h3 i).exists.choose_spec
  have hlamu : ∀ i s, c s i = c s (i + 3) → s = lam i := fun i s h => (h3 i).unique h (hlam i)
  -- integer positions
  set L : ℤ → Fin 3 := fun k => lam (k : ZMod n) with hLdef
  set W : ℤ → ℤ → Prop := fun k t => c (L k) (k : ZMod n) = c (L k) ((k + t : ℤ) : ZMod n) with hWdef
  have hW3 : ∀ k, W k 3 := fun k => by
    simp only [hWdef, hLdef]; rw [hlam (k : ZMod n)]; push_cast; rfl
  have hW0 : ∀ k, W k 0 := fun k => by simp [hWdef]
  have hLu : ∀ (k : ℤ) s, c s (k : ZMod n) = c s ((k + 3 : ℤ) : ZMod n) → s = L k := by
    intro k s h; apply hlamu; push_cast at h; exact h
  -- offsets inside a window lie in [0, 3]
  have hwin : ∀ k t, |t| ≤ 6 → W k t → 0 ≤ t ∧ t ≤ 3 := by
    intro k t ht h
    have h1 := hnear (L k) k t ht h
    rw [abs_le] at h1
    refine ⟨?_, h1.2⟩
    by_contra hneg
    have h2 : c (L k) ((k + t : ℤ) : ZMod n) = c (L k) (((k + t) + (3 - t) : ℤ) : ZMod n) := by
      rw [show k + t + (3 - t) = k + 3 by ring, ← h, hW3 k]
    have := hnear (L k) (k + t) (3 - t) (by rw [abs_le]; constructor <;> omega) h2
    rw [abs_le] at this; omega
  -- two windows of one layer sharing a vertex coincide
  have hshare : ∀ k d t t', |d| ≤ 3 → |t| ≤ 3 → |t'| ≤ 3 → L k = L (k + d) → W k t →
      W (k + d) t' → t = d + t' → d = 0 := by
    intro k d t t' hd ht ht' hL h h' htt
    have e1 : c (L k) (k : ZMod n) = c (L k) ((k + d : ℤ) : ZMod n) := by
      rw [h, show k + t = k + d + t' by rw [htt]; ring, hL]; exact h'.symm
    have w1 := hwin k d (by rw [abs_le] at hd ⊢; constructor <;> omega) e1
    have e2 : W (k + d) (-d) := by
      simp only [hWdef]; rw [show k + d + -d = k by ring, ← hL]; exact e1.symm
    have w2 := hwin (k + d) (-d) (by rw [abs_neg]; rw [abs_le] at hd ⊢; constructor <;> omega) e2
    omega
  have hL_period : ∀ k, L (k + n) = L k := fun k => by simp [hLdef]
  have hW_period : ∀ k t, W (k + n) t ↔ W k t := fun k t => by
    simp only [hWdef, hL_period]; push_cast; simp
  -- (1) the pair (k, k+2) lies in exactly one of the windows k-1 (offsets 1, 3) and k (offsets 0, 2)
  have step1 : ∀ k, W (k - 1) 1 ↔ ¬ W k 2 := by
    intro k
    constructor
    · intro ha hb
      have e1 : c (L (k - 1)) (k : ZMod n) = c (L (k - 1)) (((k : ℤ) + 2 : ℤ) : ZMod n) := by
        have := hW3 (k - 1); simp only [hWdef] at ha this
        rw [show k - 1 + 1 = k by ring] at ha; rw [show k - 1 + 3 = k + 2 by ring] at this
        rw [← ha, this]
      have e2 : c (L k) (k : ZMod n) = c (L k) (((k : ℤ) + 2 : ℤ) : ZMod n) := hb
      have hs : L (k - 1) = L k := by
        have := (h2 (k : ZMod n)).unique (y₁ := L (k - 1)) (y₂ := L k) (by push_cast at e1; exact e1)
          (by push_cast at e2; exact e2)
        exact this
      have := hshare (k - 1) 1 3 2 (by norm_num) (by norm_num) (by norm_num)
        (by rw [show k - 1 + 1 = k by ring]; exact hs) (hW3 _)
        (by rw [show k - 1 + 1 = k by ring]; exact hb) (by norm_num)
      norm_num at this
    · intro hb
      obtain ⟨s, hs, -⟩ := h2 (k : ZMod n)
      obtain ⟨d, hd, hd3, hdk⟩ := hspan s (k : ZMod n)
      have cast1 : (k : ZMod n) - (d : ℕ) = ((k - d : ℤ) : ZMod n) := by push_cast; ring
      rw [cast1] at hd3 hdk
      have hsL : s = L (k - d) := hLu _ _ (by push_cast at hd3 ⊢; rw [hd3])
      subst hsL
      have hmemd : W (k - d) (d + 2) := by
        simp only [hWdef]; rw [show k - d + (d + 2) = k + 2 by ring, hdk]
        push_cast at hs ⊢; exact hs
      have := hwin (k - d) (d + 2) (by rw [abs_le]; constructor <;> omega) hmemd
      have hd1 : d = 0 ∨ d = 1 := by omega
      rcases hd1 with rfl | rfl
      · exact absurd (by simpa [hWdef] using hmemd) hb
      · simp only [hWdef]; push_cast at hdk ⊢
        rw [show (k : ZMod n) - 1 + 1 = k by ring]; exact hdk
  -- windows of one layer cannot share a vertex
  have hne : ∀ k d t t', 1 ≤ d → d ≤ 3 → 0 ≤ t → t ≤ 3 → 0 ≤ t' → t' ≤ 3 → W k t →
      W (k + d) t' → t = d + t' → L k ≠ L (k + d) := by
    intro k d t t' h1 h2 h3 h4 h5 h6 hW hW' htt hL
    have := hshare k d t t' (by rw [abs_le]; constructor <;> omega) (by rw [abs_le]; constructor <;> omega)
      (by rw [abs_le]; constructor <;> omega) hL hW hW' htt
    omega
  -- every layer meets v in a window
  have hspanZ : ∀ s (v : ℤ), ∃ d : ℤ, 0 ≤ d ∧ d ≤ 3 ∧ s = L (v - d) ∧ W (v - d) d := by
    intro s v
    obtain ⟨d, hd, hd3, hdk⟩ := hspan s (v : ZMod n)
    have cast1 : (v : ZMod n) - (d : ℕ) = ((v - d : ℤ) : ZMod n) := by push_cast; ring
    rw [cast1] at hd3 hdk
    have hsL : s = L (v - d) := hLu _ _ (by push_cast at hd3 ⊢; rw [hd3])
    refine ⟨d, by omega, by omega, hsL, ?_⟩
    simp only [hWdef]; rw [← hsL, show v - (d : ℤ) + d = v by ring, hdk]
  -- (2) at each vertex exactly one of the windows v-1 (offset 1) and v-2 (offset 2) contains v
  have step2 : ∀ v, W (v - 1) 1 ↔ ¬ W (v - 2) 2 := by
    intro v
    constructor
    · intro ha hb
      have e01 := hne (v - 1) 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ha (by rw [show v - 1 + 1 = v by ring]; exact hW0 v) (by norm_num)
      have e02 := hne (v - 2) 2 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hb (by rw [show v - 2 + 2 = v by ring]; exact hW0 v) (by norm_num)
      have e03 := hne (v - 3) 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 _) (by rw [show v - 3 + 3 = v by ring]; exact hW0 v) (by norm_num)
      have e12 := hne (v - 2) 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hb (by rw [show v - 2 + 1 = v - 1 by ring]; exact ha) (by norm_num)
      have e13 := hne (v - 3) 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show v - 3 + 2 = v - 1 by ring]; exact ha) (by norm_num)
      have e23 := hne (v - 3) 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show v - 3 + 1 = v - 2 by ring]; exact hb) (by norm_num)
      simp only [show v - 1 + 1 = v by ring, show v - 2 + 2 = v by ring, show v - 3 + 3 = v by ring,
        show v - 2 + 1 = v - 1 by ring, show v - 3 + 2 = v - 1 by ring,
        show v - 3 + 1 = v - 2 by ring] at e01 e02 e03 e12 e13 e23
      exact fin3_four (L v) (L (v - 1)) (L (v - 2)) (L (v - 3)) e01.symm e02.symm e03.symm e12.symm
        e13.symm e23.symm
    · intro hb
      by_contra ha
      apply fin3_two (L v) (L (v - 3))
      intro s
      obtain ⟨d, hd0, hd3, hs, hw⟩ := hspanZ s v
      have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · left; simpa using hs
      · exact absurd hw ha
      · exact absurd hw hb
      · right; exact hs
  -- (3) the offset-1 pattern is 2-periodic
  have hper2 : ∀ k, W (k + 1) 1 ↔ W (k - 1) 1 := by
    intro k
    have h1 := step1 k
    have h2' := step2 (k + 2)
    rw [show k + 2 - 1 = k + 1 by ring, show k + 2 - 2 = k by ring] at h2'
    rw [h1, h2']
  have hb : ∀ j, W j 2 ↔ ¬ W (j - 1) 1 := fun j => by rw [step1 j, not_not]
  by_cases hA : ∃ k, (W k 1 ↔ W (k + 1) 1)
  · exfalso
    obtain ⟨k, hk⟩ := hA
    have a2 : W (k + 2) 1 ↔ W k 1 := by
      have := hper2 (k + 1)
      rw [show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by ring] at this; exact this
    have a3 : W (k + 3) 1 ↔ W k 1 := by
      have := hper2 (k + 2)
      rw [show k + 2 + 1 = k + 3 by ring, show k + 2 - 1 = k + 1 by ring] at this; rw [this, hk]
    have am1 : W (k - 1) 1 ↔ W k 1 := by rw [← hper2 k, hk]
    have b0 : W k 2 ↔ ¬ W k 1 := by rw [hb, am1]
    have b1 : W (k + 1) 2 ↔ ¬ W k 1 := by rw [hb, show k + 1 - 1 = k by ring]
    have b2 : W (k + 2) 2 ↔ ¬ W k 1 := by rw [hb, show k + 2 - 1 = k + 1 by ring, ← hk]
    have b3 : W (k + 3) 2 ↔ ¬ W k 1 := by rw [hb, show k + 3 - 1 = k + 2 by ring, a2]
    have e3 : ∀ j : ℤ, k + 1 + j = k + (1 + j) := fun j => by ring
    by_cases hα : W k 1
    · have e01 := hne k 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hα
        (hW0 _) (by norm_num)
      have e02 := hne k 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 k) (a2.mpr hα) (by norm_num)
      have e03 := hne k 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 k) (hW0 _) (by norm_num)
      have e12 := hne (k + 1) 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hk.mp hα) (hW0 _) (by norm_num)
      have e13 := hne (k + 1) 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show k + 1 + 2 = k + 3 by ring]; exact a3.mpr hα) (by norm_num)
      have e23 := hne (k + 2) 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (a2.mpr hα) (hW0 _) (by norm_num)
      simp only [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring,
        show k + 2 + 1 = k + 3 by ring] at e12 e13 e23
      exact fin3_four _ _ _ _ e01 e02 e03 e12 e13 e23
    · have e01 := hne k 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 k) (b1.mpr hα) (by norm_num)
      have e02 := hne k 2 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (b0.mpr hα) (hW0 _) (by norm_num)
      have e03 := hne k 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 k) (hW0 _) (by norm_num)
      have e12 := hne (k + 1) 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show k + 1 + 1 = k + 2 by ring]; exact b2.mpr hα) (by norm_num)
      have e13 := hne (k + 1) 2 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (b1.mpr hα) (hW0 _) (by norm_num)
      have e23 := hne (k + 2) 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show k + 2 + 1 = k + 3 by ring]; exact b3.mpr hα) (by norm_num)
      simp only [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring,
        show k + 2 + 1 = k + 3 by ring] at e12 e13 e23
      exact fin3_four _ _ _ _ e01 e02 e03 e12 e13 e23
  · push Not at hA
    have hB : ∀ k, W (k + 1) 1 ↔ ¬ W k 1 := fun k => by
      have := hA k; tauto
    -- n is even
    have hpar : ∀ j : ℕ, (W (j : ℤ) 1 ↔ (W 0 1 ↔ Even j)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring, hB, ih, Nat.even_add_one]
        tauto
    have hEven : Even n := by
      have h1 := hpar n
      have h2 := hW_period 0 1
      rw [zero_add] at h2
      tauto
    obtain ⟨N, hN⟩ := hEven
    obtain ⟨p, hp⟩ : ∃ p : ℤ, W p 1 := by
      by_cases h0 : W 0 1
      · exact ⟨0, h0⟩
      · exact ⟨0 + 1, (hB 0).mpr h0⟩
    have key : ∀ q : ℤ, W q 1 → L (q + 4) = L q ∧ L (q + 2) ≠ L q := by
      intro q hq
      have hq1 : ¬ W (q + 1) 1 := fun h => ((hB q).mp h) hq
      have hq2 : W (q + 2) 1 := by
        have := (hB (q + 1)).mpr hq1; rwa [show q + 1 + 1 = q + 2 by ring] at this
      have hb2 : W (q + 2) 2 := (hb _).mpr (by rw [show q + 2 - 1 = q + 1 by ring]; exact hq1)
      have x02 := hne q 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 q) hq2 (by norm_num)
      have x03 := hne q 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 q) (hW0 _) (by norm_num)
      have x23 := hne (q + 2) 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hq2 (hW0 _) (by norm_num)
      have y12 := hne (q + 1) 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hW3 _) (by rw [show q + 1 + 1 = q + 2 by ring]; exact hb2) (by norm_num)
      have y14 := hne (q + 1) 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hW3 _) (hW0 _) (by norm_num)
      have y24 := hne (q + 2) 2 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hb2 (hW0 _) (by norm_num)
      have z01 := hne q 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq
        (hW0 _) (by norm_num)
      simp only [show q + 2 + 1 = q + 3 by ring, show q + 1 + 1 = q + 2 by ring,
        show q + 1 + 3 = q + 4 by ring, show q + 2 + 2 = q + 4 by ring] at x23 y12 y14 y24
      exact ⟨fin3_five _ _ _ _ _ x02 x03 x23 y12 y14 y24 z01, Ne.symm x02⟩
    have hEv : ∀ j : ℕ, W (p + 2 * j) 1 := by
      intro j
      induction j with
      | zero => simpa using hp
      | succ j ih =>
        have h1 : ¬ W (p + 2 * j + 1) 1 := fun h => ((hB _).mp h) ih
        have := (hB (p + 2 * j + 1)).mpr h1
        rwa [show p + 2 * j + 1 + 1 = p + 2 * ((j + 1 : ℕ) : ℤ) by push_cast; ring] at this
    have hL2 : ∀ j : ℕ, L (p + 2 * (2 * j : ℕ)) = L p ∧ L (p + 2 * (2 * j + 1 : ℕ)) ≠ L p := by
      intro j
      induction j with
      | zero =>
        refine ⟨by simp, ?_⟩
        have := (key p hp).2; simpa using this
      | succ j ih =>
        have k1 := key _ (hEv (2 * j))
        have k2 := key _ (hEv (2 * j + 1))
        refine ⟨?_, ?_⟩
        · rw [← ih.1, ← k1.1]; congr 1; push_cast; ring
        · rw [show p + 2 * ((2 * (j + 1) + 1 : ℕ) : ℤ) = p + 2 * ((2 * j + 1 : ℕ) : ℤ) + 4 by
            push_cast; ring, k2.1]
          exact ih.2
    rcases Nat.even_or_odd N with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, by omega⟩
    · exfalso
      have h1 := (hL2 j).2
      apply h1
      have : p + 2 * ((2 * j + 1 : ℕ) : ℤ) = p + n := by
        rw [hN, ← hj]; push_cast; ring
      rw [this, hL_period]
