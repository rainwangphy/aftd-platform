import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorPathCyclicIndexTransfer
import AFTD.Kb.Tcs.Op874FourColorPairNormalization
import AFTD.Kb.Tcs.Op874OffPaletteEvenWordFactorPath
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate
import AFTD.Kb.Tcs.Op874FactorPath

/-!
# odd_cycle_off_palette_factor_word

Topic: graphs   Node: 414a0db795cc

Provenance: helper lemma. OP-874 one-defect factor-word reduction, experiment 35116.

An odd cycle with an off-palette demand admits a proper demand-covering factor word with the special boundary constraints and the remaining defect color present on an interior edge.
-/

open In1051Cert
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem in1081_demand_decompose (n : ℕ) [NeZero n] (hn : 3 ≤ n) (d : Fin n → Fin 4) :
    (List.ofFn fun i : Fin (n-2) => d (Fin.ofNat n (i.val+1))) =
      d 1 :: (List.ofFn fun i : Fin (n-3) => d (Fin.ofNat n (i.val+2))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h2 : 3 + k - 2 = k + 1 := by omega
  have h3 : 3 + k - 3 = k := by omega
  simp only [h2, h3]
  rw [List.ofFn_succ]
  congr 1

theorem in1081_off_demand_in_path (n : ℕ) [NeZero n] (hn : 3 ≤ n) (d : Fin n → Fin 4)
    (hoff : ∃ i : Fin n, i ≠ 0 ∧ 2 ≤ (d i).val) :
    2 ≤ (d 1).val ∨ 2 ≤ (d (-1)).val ∨
      ∃ z ∈ (List.ofFn fun i : Fin (n-3) => d (Fin.ofNat n (i.val+2))).reverse,
        2 ≤ z.val := by
  obtain ⟨i, hi0, hi⟩ := hoff
  by_cases hi1 : i = 1
  · exact Or.inl (hi1 ▸ hi)
  by_cases hilast : i = -1
  · exact Or.inr (Or.inl (hilast ▸ hi))
  right; right
  have hv0 : i.val ≠ 0 := by
    intro h
    apply hi0
    apply Fin.ext
    simpa using h
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hv1 : i.val ≠ 1 := by
    intro h
    apply hi1
    apply Fin.ext
    change i.val = (1 : Fin n).val
    rw [hone]
    exact h
  have hlast : (-1 : Fin n).val = n - 1 := by
    rw [Fin.val_neg']
    rw [hone, Nat.mod_eq_of_lt (by omega)]
  have hvlast : i.val ≠ n - 1 := by
    intro h
    apply hilast
    exact Fin.ext (h.trans hlast.symm)
  have hlow : 2 ≤ i.val := by omega
  have hhigh : i.val < n - 1 := by have := i.isLt; omega
  let j : Fin (n-3) := ⟨i.val - 2, by omega⟩
  refine ⟨d i, ?_, hi⟩
  rw [List.mem_reverse, List.mem_ofFn]
  refine ⟨j, ?_⟩
  congr 1
  apply Fin.ext
  simp only [Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt (by dsimp [j]; omega)]
  dsimp [j]
  omega
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open In1051Cert

def in1081_transfer_statement : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (d : Fin n → Fin 4)
    (a b u : Fin 4) (last firstC : ℕ) (rest : List ℕ)
    (hab : a ≠ b) (hlast : last < 4) (hlastneq : last ≠ a.val)
    (hfirst : firstC ≠ a.val) (hu : u.val ∈ firstC :: rest)
    (hpath : FactorPath b.val (List.ofFn fun i : Fin (n-2) => d (Fin.ofNat n (i.val+1)))
      (firstC :: rest) last)
    (hfinal : (d (-1)).val = last ∨ d (-1) = a),
    ∃ c : Fin n → Fin 4,
      c (-1) = a ∧ c 0 = b ∧
      (∀ i, c (i-1) ≠ c i) ∧
      (∀ i, i ≠ 0 → d i = c (i-1) ∨ d i = c i) ∧
      c 1 ≠ a ∧ (∃ i, i ≠ 0 ∧ i+1 ≠ 0 ∧ c i = u)

theorem odd_cycle_off_palette_factor_word (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) (d : Fin n → Fin 4) (a b : Fin 4) (hab : a ≠ b) (hoff : ∃ i : Fin n, i ≠ 0 ∧ d i ≠ a ∧ d i ≠ b) : ∃ (c : Fin n → Fin 4) (t u : Fin 4), (∀ i, c (i - 1) ≠ c i) ∧ (∀ i, i ≠ 0 → d i = c (i - 1) ∨ d i = c i) ∧ (t = a ∨ t = b) ∧ t ≠ u ∧ t ≠ c (-1) ∧ t ≠ c 0 ∧ u ≠ c (-1) ∧ u ≠ c 0 ∧ c 1 ≠ c (-1) ∧ (∃ i : Fin n, i ≠ 0 ∧ i + 1 ≠ 0 ∧ c i = u) := by
  have htransfer : in1081_transfer_statement := by
    intro n inst hn d a b u last firstC rest hab hlast hlastneq hfirst hu hpath hfinal
    exact op874_factor_path_cyclic_index_transfer n hn d a b u last firstC rest hab hlast hlastneq hfirst hu hpath hfinal
  obtain ⟨σ, hσa, hσb⟩ := op874_four_color_pair_normalization a b hab
  let D : Fin n → Fin 4 := fun i => σ (d i)
  have hoff' : ∃ i : Fin n, i ≠ 0 ∧ 2 ≤ (D i).val := by
    obtain ⟨i, hi, hia, hib⟩ := hoff
    have h0 : D i ≠ 0 := by
      intro h
      apply hia
      apply σ.injective
      exact h.trans hσa.symm
    have h1 : D i ≠ 1 := by
      intro h
      apply hib
      apply σ.injective
      exact h.trans hσb.symm
    have hv0 : (D i).val ≠ 0 := by
      intro h
      apply h0
      apply Fin.ext
      exact h
    have hv1 : (D i).val ≠ 1 := by
      intro h
      apply h1
      apply Fin.ext
      exact h
    refine ⟨i, hi, ?_⟩
    have := (D i).isLt
    omega
  let ds : List (Fin 4) :=
    (List.ofFn fun i : Fin (n-3) => D (Fin.ofNat n (i.val+2))).reverse
  have heven : (ds.length + 2) % 2 = 0 := by
    dsimp [ds]
    simp only [List.length_reverse, List.length_ofFn]
    obtain ⟨k, hk⟩ := hodd
    omega
  have hoffds : 2 ≤ (D 1).val ∨ 2 ≤ (D (-1)).val ∨ ∃ z ∈ ds, 2 ≤ z.val := by
    exact in1081_off_demand_in_path n hn D hoff'
  obtain ⟨x, firstC, rest, hx, hfirst, hpath, hlast, hfinal, hinterior⟩ :=
    op874_off_palette_even_word_factor_path (D 1) (D (-1)) ds heven hoffds
  rcases hx with ⟨ha, hb, hu, hc, hab', hau, hbu, t, ht2, hta, htb, htu⟩
  let a0 : Fin 4 := ⟨x.a, ha⟩
  let b0 : Fin 4 := ⟨x.b, hb⟩
  let u0 : Fin 4 := ⟨x.u, hu⟩
  let t0 : Fin 4 := ⟨t, by omega⟩
  have hab0 : a0 ≠ b0 := by
    intro h
    apply hab'
    exact congrArg Fin.val h
  have hpath' : FactorPath b0.val (List.ofFn fun i : Fin (n-2) => D (Fin.ofNat n (i.val+1)))
      (firstC :: rest) x.c := by
    rw [in1081_demand_decompose n hn D]
    simpa [ds] using hpath
  have hfinal' : (D (-1)).val = x.c ∨ D (-1) = a0 := by
    rcases hfinal with h | h
    · exact Or.inl h
    · exact Or.inr (Fin.ext h)
  have hfirst' : firstC ≠ a0.val := hfirst
  have hlast' : x.c ≠ a0.val := hlast
  have hinterior' : u0.val ∈ firstC :: rest := hinterior
  obtain ⟨c0, hca, hcb, hcproper, hcdemand, hcfirst, hcu⟩ :=
    htransfer n hn D a0 b0 u0 x.c firstC rest hab0 hc hlast' hfirst' hinterior' hpath' hfinal'
  have ht01 : t0 = 0 ∨ t0 = 1 := by
    by_cases ht : t = 0
    · left; apply Fin.ext; exact ht
    · right; apply Fin.ext; change t = 1; omega
  have htu0 : t0 ≠ u0 := by intro h; exact htu (congrArg Fin.val h)
  have hta0 : t0 ≠ a0 := by intro h; exact hta (congrArg Fin.val h)
  have htb0 : t0 ≠ b0 := by intro h; exact htb (congrArg Fin.val h)
  have hua0 : u0 ≠ a0 := by intro h; exact hau (congrArg Fin.val h).symm
  have hub0 : u0 ≠ b0 := by intro h; exact hbu (congrArg Fin.val h).symm
  refine ⟨fun i => σ.symm (c0 i), σ.symm t0, σ.symm u0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    exact hcproper i (σ.symm.injective h)
  · intro i hi
    rcases hcdemand i hi with h | h
    · left; simpa [D] using congrArg σ.symm h
    · right; simpa [D] using congrArg σ.symm h
  · rcases ht01 with ht | ht
    · left; apply σ.injective; simpa [ht, hσa]
    · right; apply σ.injective; simpa [ht, hσb]
  · intro h; exact htu0 (σ.symm.injective h)
  · intro h; apply hta0; simpa [hca] using σ.symm.injective h
  · intro h; apply htb0; simpa [hcb] using σ.symm.injective h
  · intro h; apply hua0; simpa [hca] using σ.symm.injective h
  · intro h; apply hub0; simpa [hcb] using σ.symm.injective h
  · intro h; apply hcfirst; simpa [hca] using σ.symm.injective h
  · obtain ⟨i, hi, hip, h⟩ := hcu
    exact ⟨i, hi, hip, congrArg σ.symm h⟩
