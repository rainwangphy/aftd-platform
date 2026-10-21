import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerSevenTightTypeSequenceOneIffSix
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenCoverFourLayerWeightEq
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenLayerWeightEqClassFiveImpOneTwoImpSix
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt

/-!
# simple_graph_cycle_power_seven_cover_four_tight_one_iff_six

Topic: graphs   Node: 3be09cad543e

Provenance: helper lemma. step for simple_graph_cycle_power_seven_cover_four_tight_dvd (research thread RT-1, open case k = 7 of OP-205, arXiv:2610.15635)

In a tight cover of C_n^7 (n ≥ 22) by 4 equivalence subgraphs (every distance-7, 6, 4 pair covered exactly once, every class spanned by a distance-7 pair), the class starting at i contains i+1 exactly when it contains i+6: the hypothesis h16 of simple_graph_cycle_power_seven_cover_four_tight_alternate holds automatically.
-/

theorem simple_graph_cycle_power_seven_cover_four_tight_one_iff_six (n : ℕ) [NeZero n]
    (hn : 22 ≤ n) (c : Fin 4 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 7).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n 7).Adj u v → ∃ s, c s u = c s v)
    (h7 : ∀ i, ∃! s, c s i = c s (i + 7)) (h6 : ∀ i, ∃! s, c s i = c s (i + 6))
    (h4 : ∀ i, ∃! s, c s i = c s (i + 4))
    (hspan : ∀ s i, ∃ d : ℕ, d ≤ 7 ∧ c s (i - d) = c s (i - d + 7) ∧ c s (i - d) = c s i) :
    ∀ s i, c s i = c s (i + 7) → (c s i = c s (i + 1) ↔ c s i = c s (i + 6)) := by
  have hinj : ∀ a b : ℤ, a - b < n → b - a < n → (a : ZMod n) = (b : ZMod n) → a = b :=
    fun a b h1 h2 e => (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b
      (by rw [abs_lt]; constructor <;> omega)).mp e
  have hnat : ∀ a b : ℕ, a < n → b < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b ha hb e
    rw [ZMod.natCast_eq_natCast_iff'] at e
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  -- every member of a class containing p and p + 7 lies in p .. p + 7
  have hA : ∀ s p v, c s p = c s (p + 7) → c s p = c s v →
      ∃ e : ℤ, 0 ≤ e ∧ e ≤ 7 ∧ v = p + (e : ZMod n) := by
    intro s p v h1 h2
    by_cases hv : v = p
    · exact ⟨0, le_refl _, by norm_num, by simp [hv]⟩
    obtain ⟨e, he0, he7, rfl⟩ :=
      (simple_graph_cycle_power_seven_adj_iff n hn p v).mp (hc s p v (Ne.symm hv) h2)
    rw [abs_le] at he7
    by_cases hv7 : p + (e : ZMod n) = p + 7
    · have h' : (e : ZMod n) = ((7 : ℤ) : ZMod n) := by push_cast; linear_combination hv7
      have := hinj e 7 (by omega) (by omega) h'
      exact ⟨e, by omega, by omega, rfl⟩
    · obtain ⟨e', _, he'7, he'⟩ := (simple_graph_cycle_power_seven_adj_iff n hn (p + 7) (p + e)).mp
        (hc s (p + 7) (p + e) (Ne.symm hv7) (h1.symm.trans h2))
      rw [abs_le] at he'7
      have h' : (e : ZMod n) = ((7 + e' : ℤ) : ZMod n) := by push_cast; linear_combination he'
      have := hinj e (7 + e') (by omega) (by omega) h'
      exact ⟨e, by omega, by omega, rfl⟩
  -- two classes of one layer, each spanned by a distance-7 pair, that meet are the same
  have hE : ∀ s (p q w : ZMod n), c s p = c s (p + 7) → c s q = c s (q + 7) →
      c s p = c s w → c s q = c s w → p = q := by
    intro s p q w hp hq hpw hqw
    obtain ⟨e, he0, he7, rfl⟩ := hA s p q hp (hpw.trans hqw.symm)
    obtain ⟨e', he'0, he'7, he'⟩ := hA s p (p + e + 7) hp (hpw.trans (hqw.symm.trans hq))
    have h' : ((e + 7 : ℤ) : ZMod n) = (e' : ZMod n) := by push_cast; linear_combination he'
    have := hinj (e + 7) e' (by omega) (by omega) h'
    have he : e = 0 := by omega
    simp [he]
  have h7' : ∀ i, ∃ s, c s i = c s (i + 7) ∧ ∀ t, c t i = c t (i + 7) → t = s := fun i => h7 i
  choose σ hσ hσu using h7'
  -- a pair at distance d covered by layer s lies in the class starting at some u - a
  have hD : ∀ (s : Fin 4) (u : ZMod n) (d : ℕ), d ≤ 7 → c s u = c s (u + d) →
      ∃ a : ℕ, a + d ≤ 7 ∧ σ (u - a) = s ∧ c s (u - a) = c s u ∧ c s (u - a) = c s (u + d) := by
    intro s u d hd h
    obtain ⟨d0, hd0, hsp7, hspu⟩ := hspan s u
    have hs : s = σ (u - d0) := hσu (u - d0) s hsp7
    obtain ⟨e, he0, he7, he⟩ := hA s (u - d0) (u + d) hsp7 (hspu.trans h)
    have h' : ((d : ℤ) : ZMod n) = ((e - d0 : ℤ) : ZMod n) := by push_cast; linear_combination he
    have := hinj d (e - d0) (by omega) (by omega) h'
    exact ⟨d0, by omega, hs.symm, hspu, hspu.trans h⟩
  have hsub : ∀ (u : ZMod n) (a b : ℕ), a ≤ 7 → b ≤ 7 → u - (a : ZMod n) = u - (b : ZMod n) → a = b :=
    fun u a b ha hb e => hnat a b (by omega) (by omega) (sub_right_injective e)

  obtain ⟨x, hx⟩ : ∃ x : ZMod n → Fin 8 → Bool,
      ∀ p j, x p j = decide (c (σ p) p = c (σ p) (p + ((j : ℕ) : ZMod n))) := ⟨_, fun _ _ => rfl⟩
  have hxs : ∀ (p : ZMod n) (j : Fin 8) (q : ZMod n), p + ((j : ℕ) : ZMod n) = q →
      (x p j = true ↔ c (σ p) p = c (σ p) q) := by
    intro p j q h; rw [hx, ← h]; simp
  -- σ is determined by any distance-7 pair
  have hσeq : ∀ s p, c s p = c s (p + 7) → σ p = s := fun s p h => (hσu p s h).symm
  -- two classes starting at u - a and u - b both containing u and u + d, with d covered once
  have hU : ∀ (u : ZMod n) (d a b : ℕ), a ≤ 7 → b ≤ 7 →
      (∀ s t, c s u = c s (u + d) → c t u = c t (u + d) → s = t) →
      c (σ (u - a)) (u - a) = c (σ (u - a)) u → c (σ (u - a)) (u - a) = c (σ (u - a)) (u + d) →
      c (σ (u - b)) (u - b) = c (σ (u - b)) u → c (σ (u - b)) (u - b) = c (σ (u - b)) (u + d) →
      a = b := by
    intro u d a b ha hb huniq h1 h2 h3 h4
    have hst : σ (u - a) = σ (u - b) := huniq _ _ (h1.symm.trans h2) (h3.symm.trans h4)
    have hb7 := hσ (u - b)
    rw [← hst] at hb7 h3
    exact hsub u a b ha hb (hE _ _ _ u (hσ _) hb7 h1 h3)
  have hcov' : ∀ (d : ℕ) (u : ZMod n), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, x (u - j.val) j = true ∧
        x (u - j.val) ⟨j.val + d, by omega⟩ = true := by
    intro d u hd
    have hd7 : d ≤ 7 := by simp at hd; omega
    have hadj : (simple_graph_cycle_power n 7).Adj u (u + (d : ZMod n)) := by
      rw [simple_graph_cycle_power_seven_adj_iff n hn]
      refine ⟨d, ?_, ?_, by push_cast; rfl⟩
      · simp at hd; omega
      · rw [abs_le]; constructor <;> omega
    obtain ⟨s, hs⟩ := hcov u _ hadj
    obtain ⟨a, ha, hσa, h1, h2⟩ := hD s u d hd7 hs
    refine ⟨⟨a, by omega⟩, ha, ?_, ?_⟩
    · rw [hxs _ _ u (by simp)]; rw [hσa]; exact h1
    · rw [hxs _ _ (u + d) (by simp; ring)]; rw [hσa]; exact h2
  have hd6' : ∀ u, (x (u - 1) 1).toNat + (x u 6).toNat = 1 := by
    intro u
    have e1 := hxs (u - 1) 1 u (by simp)
    have e6 := hxs u 6 (u + 6) (by show u + ((6 : ℕ) : ZMod n) = u + 6; push_cast; ring)
    obtain ⟨s0, hs0, hs0u⟩ := h6 u
    have huniq : ∀ s t, c s u = c s (u + ((6 : ℕ) : ZMod n)) → c t u = c t (u + ((6 : ℕ) : ZMod n)) → s = t := by
      intro s t hs ht; push_cast at hs ht; exact (hs0u s hs).trans (hs0u t ht).symm
    have P1 : x (u - 1) 1 = true ↔ (c (σ (u - ((1 : ℕ) : ZMod n))) (u - ((1 : ℕ) : ZMod n)) = c (σ (u - ((1 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((1 : ℕ) : ZMod n))) (u - ((1 : ℕ) : ZMod n)) = c (σ (u - ((1 : ℕ) : ZMod n))) (u + ((6 : ℕ) : ZMod n))) := by
      rw [e1]; push_cast
      constructor
      · intro h; refine ⟨h, (hσ (u - 1)).trans ?_⟩
        congr 1; ring
      · exact fun h => h.1
    have P6 : x u 6 = true ↔ (c (σ (u - ((0 : ℕ) : ZMod n))) (u - ((0 : ℕ) : ZMod n)) = c (σ (u - ((0 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((0 : ℕ) : ZMod n))) (u - ((0 : ℕ) : ZMod n)) = c (σ (u - ((0 : ℕ) : ZMod n))) (u + ((6 : ℕ) : ZMod n))) := by
      rw [e6]; push_cast; simp
    obtain ⟨a, ha, hσa, h1, h2⟩ := hD s0 u 6 (by norm_num) (by push_cast; exact hs0)
    have hex : x (u - 1) 1 = true ∨ x u 6 = true := by
      have : a ≤ 1 := by omega
      interval_cases a
      · right; rw [P6]; rw [hσa]; exact ⟨h1, h2⟩
      · left; rw [P1]; rw [hσa]; exact ⟨h1, h2⟩
    have hne : ¬ (x (u - 1) 1 = true ∧ x u 6 = true) := by
      rintro ⟨q1, q6⟩
      rw [P1] at q1; rw [P6] at q6
      have := hU u 6 1 0 (by norm_num) (by norm_num) huniq q1.1 q1.2 q6.1 q6.2
      omega
    revert hex hne
    generalize x (u - 1) 1 = b1; generalize x u 6 = b6
    revert b1 b6; decide

  have hd4' : ∀ u, (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat +
      (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3).toNat = 1 := by
    intro u
    obtain ⟨s0, hs0, hs0u⟩ := h4 u
    have huniq : ∀ s t, c s u = c s (u + ((4 : ℕ) : ZMod n)) → c t u = c t (u + ((4 : ℕ) : ZMod n)) → s = t := by
      intro s t hs ht; push_cast at hs ht; exact (hs0u s hs).trans (hs0u t ht).symm
    have P0 : x u 4 = true ↔ (c (σ (u - ((0 : ℕ) : ZMod n))) (u - ((0 : ℕ) : ZMod n)) = c (σ (u - ((0 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((0 : ℕ) : ZMod n))) (u - ((0 : ℕ) : ZMod n)) = c (σ (u - ((0 : ℕ) : ZMod n))) (u + ((4 : ℕ) : ZMod n))) := by
      rw [hxs u 4 (u + 4) (by show u + ((4 : ℕ) : ZMod n) = u + 4; push_cast; ring)]; push_cast; simp
    have P1 : (x (u - 1) 1 && x (u - 1) 5) = true ↔ (c (σ (u - ((1 : ℕ) : ZMod n))) (u - ((1 : ℕ) : ZMod n)) = c (σ (u - ((1 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((1 : ℕ) : ZMod n))) (u - ((1 : ℕ) : ZMod n)) = c (σ (u - ((1 : ℕ) : ZMod n))) (u + ((4 : ℕ) : ZMod n))) := by
      rw [Bool.and_eq_true, hxs (u - 1) 1 u (by simp),
        hxs (u - 1) 5 (u + 4) (by show u - 1 + ((5 : ℕ) : ZMod n) = u + 4; push_cast; ring)]
      push_cast; exact Iff.rfl
    have P2 : (x (u - 2) 2 && x (u - 2) 6) = true ↔ (c (σ (u - ((2 : ℕ) : ZMod n))) (u - ((2 : ℕ) : ZMod n)) = c (σ (u - ((2 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((2 : ℕ) : ZMod n))) (u - ((2 : ℕ) : ZMod n)) = c (σ (u - ((2 : ℕ) : ZMod n))) (u + ((4 : ℕ) : ZMod n))) := by
      rw [Bool.and_eq_true, hxs (u - 2) 2 u (by show u - 2 + ((2 : ℕ) : ZMod n) = u; push_cast; ring),
        hxs (u - 2) 6 (u + 4) (by show u - 2 + ((6 : ℕ) : ZMod n) = u + 4; push_cast; ring)]
      push_cast; exact Iff.rfl
    have P3 : x (u - 3) 3 = true ↔ (c (σ (u - ((3 : ℕ) : ZMod n))) (u - ((3 : ℕ) : ZMod n)) = c (σ (u - ((3 : ℕ) : ZMod n))) u ∧
        c (σ (u - ((3 : ℕ) : ZMod n))) (u - ((3 : ℕ) : ZMod n)) = c (σ (u - ((3 : ℕ) : ZMod n))) (u + ((4 : ℕ) : ZMod n))) := by
      rw [hxs (u - 3) 3 u (by show u - 3 + ((3 : ℕ) : ZMod n) = u; push_cast; ring)]
      push_cast
      constructor
      · intro h; refine ⟨h, (hσ (u - 3)).trans ?_⟩
        congr 1; ring
      · exact fun h => h.1
    have hR : ∀ a b : ℕ, a ≤ 3 → b ≤ 3 →
        (c (σ (u - a)) (u - a) = c (σ (u - a)) u ∧ c (σ (u - a)) (u - a) = c (σ (u - a)) (u + ((4 : ℕ) : ZMod n))) →
        (c (σ (u - b)) (u - b) = c (σ (u - b)) u ∧ c (σ (u - b)) (u - b) = c (σ (u - b)) (u + ((4 : ℕ) : ZMod n))) →
        a = b := fun a b ha hb ra rb => hU u 4 a b (by omega) (by omega) huniq ra.1 ra.2 rb.1 rb.2
    obtain ⟨a, ha, hσa, h1, h2⟩ := hD s0 u 4 (by norm_num) (by push_cast; exact hs0)
    have hex : x u 4 = true ∨ (x (u - 1) 1 && x (u - 1) 5) = true ∨
        (x (u - 2) 2 && x (u - 2) 6) = true ∨ x (u - 3) 3 = true := by
      have : a ≤ 3 := by omega
      interval_cases a
      · left; rw [P0, hσa]; exact ⟨h1, h2⟩
      · right; left; rw [P1, hσa]; exact ⟨h1, h2⟩
      · right; right; left; rw [P2, hσa]; exact ⟨h1, h2⟩
      · right; right; right; rw [P3, hσa]; exact ⟨h1, h2⟩
    have n01 : ¬ (x u 4 = true ∧ (x (u - 1) 1 && x (u - 1) 5) = true) := fun h =>
      absurd (hR 0 1 (by norm_num) (by norm_num) (P0.mp h.1) (P1.mp h.2)) (by norm_num)
    have n02 : ¬ (x u 4 = true ∧ (x (u - 2) 2 && x (u - 2) 6) = true) := fun h =>
      absurd (hR 0 2 (by norm_num) (by norm_num) (P0.mp h.1) (P2.mp h.2)) (by norm_num)
    have n03 : ¬ (x u 4 = true ∧ x (u - 3) 3 = true) := fun h =>
      absurd (hR 0 3 (by norm_num) (by norm_num) (P0.mp h.1) (P3.mp h.2)) (by norm_num)
    have n12 : ¬ ((x (u - 1) 1 && x (u - 1) 5) = true ∧ (x (u - 2) 2 && x (u - 2) 6) = true) := fun h =>
      absurd (hR 1 2 (by norm_num) (by norm_num) (P1.mp h.1) (P2.mp h.2)) (by norm_num)
    have n13 : ¬ ((x (u - 1) 1 && x (u - 1) 5) = true ∧ x (u - 3) 3 = true) := fun h =>
      absurd (hR 1 3 (by norm_num) (by norm_num) (P1.mp h.1) (P3.mp h.2)) (by norm_num)
    have n23 : ¬ ((x (u - 2) 2 && x (u - 2) 6) = true ∧ x (u - 3) 3 = true) := fun h =>
      absurd (hR 2 3 (by norm_num) (by norm_num) (P2.mp h.1) (P3.mp h.2)) (by norm_num)
    revert hex n01 n02 n03 n12 n13 n23
    generalize x u 4 = b0; generalize (x (u - 1) 1 && x (u - 1) 5) = b1
    generalize (x (u - 2) 2 && x (u - 2) 6) = b2; generalize x (u - 3) 3 = b3
    revert b0 b1 b2 b3; decide
  have hcount' : ∀ u, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat +
      (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat = 2 := by
    intro u
    have hQ : ∀ j : Fin 8, x (u - (j : ℕ)) j = true ↔
        c (σ (u - (j : ℕ))) (u - (j : ℕ)) = c (σ (u - (j : ℕ))) u := fun j => hxs _ _ u (by simp)
    have h7u : c (σ (u - 7)) (u - 7) = c (σ (u - 7)) u := by
      have := hσ (u - 7); rwa [sub_add_cancel] at this
    have hne_start : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → c (σ (u - k)) (u - k) = c (σ (u - k)) u → σ (u - k) ≠ σ u := by
      intro k hk1 hk6 hq heq
      have h1 := hσ (u - k); rw [heq] at h1 hq
      have := hE (σ u) (u - k) u u h1 (hσ u) hq rfl
      have := hsub u k 0 (by omega) (by omega) (by simpa using this)
      omega
    have hne_end : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → c (σ (u - k)) (u - k) = c (σ (u - k)) u → σ (u - k) ≠ σ (u - 7) := by
      intro k hk1 hk6 hq heq
      have h1 := hσ (u - k); rw [heq] at h1 hq
      have := hE (σ (u - 7)) (u - k) (u - 7) u h1 (hσ (u - 7)) hq h7u
      have := hsub u k 7 (by omega) (by omega) (by push_cast; exact this)
      omega
    have hse : σ u ≠ σ (u - 7) := by
      intro heq
      have h2 : c (σ (u - 7)) u = c (σ (u - 7)) (u + 7) := by rw [← heq]; exact hσ u
      have := hE (σ (u - 7)) (u - 7) u u (hσ (u - 7)) h2 h7u rfl
      have := hsub u 7 0 (by omega) (by omega) (by simpa using this)
      omega
    have hinjk : ∀ j k : ℕ, j ≤ 7 → k ≤ 7 → c (σ (u - j)) (u - j) = c (σ (u - j)) u →
        c (σ (u - k)) (u - k) = c (σ (u - k)) u → σ (u - j) = σ (u - k) → j = k := by
      intro j k hj hk qj qk heq
      have h1 := hσ (u - k); rw [← heq] at h1 qk
      exact hsub u j k hj hk (hE _ _ _ u (hσ _) h1 qj qk)
    have hsurj : ∀ s, s ≠ σ u → s ≠ σ (u - 7) → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6 ∧
        c (σ (u - k)) (u - k) = c (σ (u - k)) u ∧ σ (u - k) = s := by
      intro s hs1 hs2
      obtain ⟨d0, hd0, hsp7, hspu⟩ := hspan s u
      have hσd := hσeq s _ hsp7
      refine ⟨d0, ?_, ?_, by rw [hσd]; exact hspu, hσd⟩
      · rcases Nat.eq_zero_or_pos d0 with h | h
        · subst h; exfalso; apply hs1; rw [← hσd]; simp
        · omega
      · by_contra h
        have h7' : d0 = 7 := by omega
        subst h7'; apply hs2; rw [← hσd]; simp
    let K : Finset (Fin 8) := Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val ≤ 6 ∧ x (u - (j : ℕ)) j = true)
    let T : Finset (Fin 4) := Finset.univ.filter (fun s => s ≠ σ u ∧ s ≠ σ (u - 7))
    have hT : T.card = 2 := by
      have key : ∀ a e : Fin 4, a ≠ e → (Finset.univ.filter (fun s => s ≠ a ∧ s ≠ e)).card = 2 := by
        decide
      exact key _ _ hse
    have hKT : K.card = T.card := by
      refine Finset.card_bij (s := K) (t := T) (fun (j : Fin 8) _ => σ (u - ((j : ℕ) : ZMod n))) ?_ ?_ ?_
      · intro j hj
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        have hq := (hQ j).mp hj.2.2
        exact ⟨hne_start j hj.1 hj.2.1 hq, hne_end j hj.1 hj.2.1 hq⟩
      · intro j hj k hk heq
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
        exact Fin.ext (hinjk j k (by omega) (by omega) ((hQ j).mp hj.2.2) ((hQ k).mp hk.2.2) heq)
      · intro s hs
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        obtain ⟨k, hk1, hk6, hq, hσk⟩ := hsurj s hs.1 hs.2
        refine ⟨⟨k, by omega⟩, ?_, hσk⟩
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hk1, hk6, (hQ ⟨k, by omega⟩).mpr hq⟩
    have hK : K.card = 2 := hKT.trans hT
    simp only [K] at hK
    rw [Finset.card_filter, Fin.sum_univ_eight] at hK
    simp at hK
    revert hK
    generalize x (u - 1) 1 = b1; generalize x (u - 2) 2 = b2; generalize x (u - 3) 3 = b3
    generalize x (u - 4) 4 = b4; generalize x (u - 5) 5 = b5; generalize x (u - 6) 6 = b6
    revert b1 b2 b3 b4 b5 b6; decide
  have hx0 : ∀ p, x p 0 = true := fun p => (hxs p 0 p (by simp)).mpr rfl
  have hx7 : ∀ p, x p 7 = true := fun p =>
    (hxs p 7 (p + 7) (by show p + ((7 : ℕ) : ZMod n) = p + 7; push_cast; ring)).mpr (hσ p)
  have hcls : ∀ p, (c (σ p) p = c (σ p) (p + 5) → c (σ p) p = c (σ p) (p + 1)) ∧
      (c (σ p) p = c (σ p) (p + 2) → c (σ p) p = c (σ p) (p + 6)) := fun p =>
    simple_graph_cycle_power_seven_layer_weight_eq_class_five_imp_one_two_imp_six n hn (c (σ p)) (hc (σ p)) (simple_graph_cycle_power_seven_cover_four_layer_weight_eq n hn c hc hcov (σ p)) p (hσ p)
  have h51' : ∀ p, x p 5 = true → x p 1 = true := by
    intro p h
    rw [hxs p 5 (p + 5) (by show p + ((5 : ℕ) : ZMod n) = p + 5; push_cast; ring)] at h
    rw [hxs p 1 (p + 1) (by simp)]
    exact (hcls p).1 h
  have h26' : ∀ p, x p 2 = true → x p 6 = true := by
    intro p h
    rw [hxs p 2 (p + 2) (by show p + ((2 : ℕ) : ZMod n) = p + 2; push_cast; ring)] at h
    rw [hxs p 6 (p + 6) (by show p + ((6 : ℕ) : ZMod n) = p + 6; push_cast; ring)]
    exact (hcls p).2 h
  have key := cycle_power_seven_tight_type_sequence_one_iff_six n x hx0 hx7 hcount' hd4' hd6' hcov' h51' h26'
  intro s i hs
  have hsi := hσeq s i hs
  have e1 := hxs i 1 (i + 1) (by simp)
  have e6 := hxs i 6 (i + 6) (by show i + ((6 : ℕ) : ZMod n) = i + 6; push_cast; ring)
  rw [hsi] at e1 e6
  constructor
  · intro h; rw [← e6, ← key i]; exact e1.mpr h
  · intro h; rw [← e1, key i]; exact e6.mpr h
