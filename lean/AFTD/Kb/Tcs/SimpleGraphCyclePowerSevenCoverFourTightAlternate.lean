import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt

/-!
# simple_graph_cycle_power_seven_cover_four_tight_alternate

Topic: graphs   Node: 2993cd409e15

Provenance: helper lemma. for RT-1 (simple_graph_cycle_power_seven_cover_four_tight_dvd): the alternation rule seen in all 288 rigid windows (exp 1947); h16 holds for the five class types that occur (exp 1554)

In a tight cover of C_n^7 (n >= 22) by 4 equivalence subgraphs in which every class starting at i (the class of the distance-7 pair (i, i+7)) contains i+1 exactly when it contains i+6, the classes alternate: the class starting at i contains i+1 if and only if the class starting at i+1 does not contain i+2. So classes {i, i+7} and larger classes alternate along the cycle.
-/

lemma simple_graph_cycle_power_seven_cover_four_tight_alternate_side
    (n : ℕ) [NeZero n] (hn : 22 ≤ n) (c : Fin 4 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 7).Adj u v)
    (hspan : ∀ s i, ∃ d : ℕ, d ≤ 7 ∧ c s (i - d) = c s (i - d + 7) ∧ c s (i - d) = c s i)
    (h16 : ∀ s i, c s i = c s (i + 7) → (c s i = c s (i + 1) ↔ c s i = c s (i + 6)))
    (s : Fin 4) (j : ZMod n) (hj : c s j = c s (j + 6)) :
    (c s (j - 1) = c s j) ∨ (c s j = c s (j + 1) ∧ c s j = c s (j + 7)) := by
  obtain ⟨d, hd7, hdA, hdB⟩ := hspan s (j + 6)
  have hchain : c s j = c s ((j + 6) - d + 7) := (hj.trans hdB.symm).trans hdA
  have hsub : (j + 6) - (d : ZMod n) + 7 - j = ((13 - (d : ℤ) : ℤ) : ZMod n) := by
    push_cast; ring
  have hne : j ≠ (j + 6) - d + 7 := by
    intro heq
    have hzero : ((13 - (d : ℤ) : ℤ) : ZMod n) = ((0 : ℤ) : ZMod n) := by
      rw [← hsub, ← heq, sub_self, Int.cast_zero]
    have hlt : |(13 : ℤ) - (d : ℤ) - (0:ℤ)| < (n : ℤ) := by
      have h1 : |(13:ℤ) - (d:ℤ)| ≤ 13 := by
        rw [abs_le]; constructor <;> omega
      calc |(13:ℤ) - (d:ℤ) - 0| = |(13:ℤ) - (d:ℤ)| := by ring_nf
        _ ≤ 13 := h1
        _ < (n:ℤ) := by omega
    have := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (13 - (d:ℤ)) 0 hlt).mp hzero
    omega
  have hadj : (simple_graph_cycle_power n 7).Adj j ((j + 6) - d + 7) := hc s j _ hne hchain
  obtain ⟨e, hene, heabs, hee⟩ :=
    (simple_graph_cycle_power_seven_adj_iff n hn j ((j + 6) - d + 7)).mp hadj
  have hcast : ((13 - (d:ℤ) : ℤ) : ZMod n) = ((e : ℤ) : ZMod n) := by
    have h2 : (j + (e : ZMod n)) - j = ((e : ℤ) : ZMod n) := by push_cast; ring
    exact hsub.symm.trans (by rw [hee]; exact h2)
  have hde : (13 : ℤ) - (d : ℤ) = e := by
    have hlt : |(13 : ℤ) - (d : ℤ) - e| < (n : ℤ) := by
      have hb := abs_le.mp heabs
      have hd7' : ((d:ℤ)) ≤ 7 := by omega
      have hd0' : (0:ℤ) ≤ (d:ℤ) := by omega
      have hle : |(13 : ℤ) - (d : ℤ) - e| ≤ 20 := by
        rw [abs_le]; constructor <;> omega
      omega
    exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (13 - (d:ℤ)) e hlt).mp hcast
  have hd67 : d = 6 ∨ d = 7 := by
    have hb := abs_le.mp heabs
    omega
  rcases hd67 with hd | hd
  · have hAj : c s j = c s (j + 7) := by
      have hA := hdA
      rw [hd] at hA
      rw [show (j + 6) - (6:ℕ) = j by ring] at hA
      exact hA
    exact Or.inr ⟨(h16 s j hAj).mpr hj, hAj⟩
  · left
    have hA := hdA
    rw [hd] at hA
    rw [show (j + 6) - (7:ℕ) = j - 1 by ring] at hA
    rw [show j - 1 + 7 = j + 6 by ring] at hA
    exact hA.trans hj.symm

theorem simple_graph_cycle_power_seven_cover_four_tight_alternate (n : ℕ) [NeZero n]
    (hn : 22 ≤ n) (c : Fin 4 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 7).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n 7).Adj u v → ∃ s, c s u = c s v)
    (h7 : ∀ i, ∃! s, c s i = c s (i + 7)) (h6 : ∀ i, ∃! s, c s i = c s (i + 6))
    (h4 : ∀ i, ∃! s, c s i = c s (i + 4))
    (hspan : ∀ s i, ∃ d : ℕ, d ≤ 7 ∧ c s (i - d) = c s (i - d + 7) ∧ c s (i - d) = c s i)
    (h16 : ∀ s i, c s i = c s (i + 7) → (c s i = c s (i + 1) ↔ c s i = c s (i + 6)))
    (i : ZMod n) :
    (∃ s, c s i = c s (i + 7) ∧ c s i = c s (i + 1)) ↔
      ¬ ∃ s, c s (i + 1) = c s (i + 1 + 7) ∧ c s (i + 1) = c s (i + 1 + 1) := by
  constructor
  · rintro ⟨s, hs7, hs1⟩ ⟨t, ht8, ht2⟩
    have hs6 : c s i = c s (i + 6) := (h16 s i hs7).mp hs1
    have ht6 : c t (i + 1) = c t (i + 1 + 6) := (h16 t (i + 1) ht8).mp ht2
    obtain ⟨s6, -, huniq⟩ := h6 (i + 1)
    have hA : c s (i + 1) = c s (i + 1 + 6) := by
      rw [show (i + 1 + 6 : ZMod n) = i + 7 by ring]
      exact hs1.symm.trans hs7
    have hst : s = t := (huniq s hA).trans (huniq t ht6).symm
    have h8t : c t i = c t (i + 8) := by
      have hs1' : c t i = c t (i + 1) := by rw [← hst]; exact hs1
      have ht8' : c t (i + 1) = c t (i + 8) := by
        rw [show (i + 1 + 7 : ZMod n) = i + 8 by ring] at ht8; exact ht8
      exact hs1'.trans ht8'
    have h8 : c s i = c s (i + 8) := by rw [hst]; exact h8t
    have hne : i ≠ i + 8 := by
      intro heq
      have hzero : ((8:ℤ) : ZMod n) = ((0:ℤ) : ZMod n) := by
        have h2 : (i + 8 : ZMod n) - i = ((8:ℤ):ZMod n) := by ring
        rw [← h2, ← heq, sub_self, Int.cast_zero]
      have hlt : |(8:ℤ) - (0:ℤ)| < (n:ℤ) := by
        have h3 : (22:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
        have h4 : |(8:ℤ) - (0:ℤ)| = 8 := by norm_num
        rw [h4]; omega
      have h8e : (8:ℤ) = 0 := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n 8 0 hlt).mp hzero
      omega
    have hadj : (simple_graph_cycle_power n 7).Adj i (i + 8) := hc s i (i + 8) hne h8
    obtain ⟨e, hene, heabs, hee⟩ := (simple_graph_cycle_power_seven_adj_iff n hn i (i + 8)).mp hadj
    have hcast : ((8:ℤ) : ZMod n) = ((e:ℤ) : ZMod n) := by
      have h1 : (i + 8 : ZMod n) - i = ((8:ℤ):ZMod n) := by ring
      have h2 : (i + (e : ZMod n)) - i = ((e:ℤ):ZMod n) := by ring
      rw [← h1, hee, h2]
    have h8e : (8:ℤ) = e := by
      apply (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n 8 e ?_).mp hcast
      have hb := abs_le.mp heabs
      have hle : |(8:ℤ) - e| ≤ 15 := by rw [abs_le]; constructor <;> omega
      have h3 : (22:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
      omega
    have hb := abs_le.mp heabs
    omega
  · intro hnr
    obtain ⟨s6, hs6, -⟩ := h6 (i + 1)
    have hkey := simple_graph_cycle_power_seven_cover_four_tight_alternate_side
      n hn c hc hspan h16 s6 (i + 1) hs6
    rcases hkey with hl | ⟨hr1, hr7⟩
    · have hl' : c s6 i = c s6 (i + 1) := by
        rw [show (i + 1 - 1 : ZMod n) = i by ring] at hl
        exact hl
      have h6' : c s6 (i + 1) = c s6 (i + 7) := by
        rw [show (i + 1 + 6 : ZMod n) = i + 7 by ring] at hs6
        exact hs6
      exact ⟨s6, hl'.trans h6', hl'⟩
    · exact absurd ⟨s6, hr7, hr1⟩ hnr
