import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrChainIffLevelSupporters
import AFTD.Kb.GameTheoryEconomics.ExistsPermWithPrefixEqTake
import AFTD.Kb.GameTheoryEconomics.EjrTwoVotersCriterion
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_chain_two_voters

Topic: social_choice   Node: 43f0faa32d67

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

For every approval profile with two voters and any number of candidates, there is an ordering of the candidates every prefix of which is an EJR committee of the corresponding size.
-/

private lemma ejr_chain_two_voters_card_fin_filter_lt {a i : ℕ} :
    (Finset.univ.filter fun j : Fin a => (j : ℕ) < i).card = min i a := by
  rcases Nat.lt_or_ge i a with h | h
  · have h1 : (Finset.univ.filter fun j : Fin a => (j : ℕ) < i) = Finset.Iio (⟨i, h⟩ : Fin a) := by
      ext j; simp [Finset.mem_Iio, Fin.lt_def]
    rw [h1, Fin.card_Iio, min_eq_left (le_of_lt h)]
  · have h1 : (Finset.univ.filter fun j : Fin a => (j : ℕ) < i) = Finset.univ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have := j.isLt; omega
    rw [h1, Finset.card_univ, Fintype.card_fin, min_eq_right h]

private lemma ejr_chain_two_voters_prefix_card {m k : ℕ} (hk : k ≤ m) (σ : Equiv.Perm (Fin m)) :
    (Finset.univ.filter fun c => (σ c : ℕ) < k).card = k := by
  rcases Nat.lt_or_ge k m with h | h
  · have h1 : (Finset.univ.filter fun c : Fin m => (σ c : ℕ) < k)
        = Finset.map (σ.symm.toEmbedding) (Finset.Iio (⟨k, h⟩ : Fin m)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding, Finset.mem_Iio, Fin.lt_def]
      constructor
      · intro hc
        exact ⟨σ c, hc, σ.symm_apply_apply c⟩
      · rintro ⟨i, hi, rfl⟩
        simp only [Equiv.apply_symm_apply]
        exact hi
    rw [h1, Finset.card_map]
    simp
  · have hkm : k = m := le_antisymm hk h
    have h2 : (Finset.univ.filter fun c : Fin m => (σ c : ℕ) < k) = Finset.univ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [hkm]; exact (σ c).isLt
    rw [h2, Finset.card_univ, Fintype.card_fin, hkm]

private lemma ejr_chain_two_voters_filter_mem_and {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x => x ∈ s ∧ p x).card = (s.filter p).card := by
  congr 1
  ext x
  simp

private lemma ejr_chain_two_voters_filter_or_card {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] (h : Disjoint s t) :
    (Finset.univ.filter fun x => (x ∈ s ∧ p x) ∨ (x ∈ t ∧ q x)).card
      = (s.filter p).card + (t.filter q).card := by
  have h1 : (Finset.univ.filter fun x => (x ∈ s ∧ p x) ∨ (x ∈ t ∧ q x))
      = (Finset.univ.filter fun x => x ∈ s ∧ p x) ∪ (Finset.univ.filter fun x => x ∈ t ∧ q x) := by
    ext x; simp
  rw [h1, Finset.card_union_of_disjoint]
  · rw [ejr_chain_two_voters_filter_mem_and, ejr_chain_two_voters_filter_mem_and]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact (Finset.disjoint_left.mp h hx.1 hx'.1)

private lemma ejr_chain_two_voters_block_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (e : ↥s ≃ Fin s.card) (kf : α → ℕ)
    (hk : kf = fun x => if h : x ∈ s then (e ⟨x, h⟩ : ℕ) else 0) (j : ℕ) :
    (Finset.univ.filter fun x => x ∈ s ∧ kf x ≤ j).card = min (j + 1) s.card := by
  rw [hk]
  have himg : (Finset.univ.filter fun x => x ∈ s ∧ (if h : x ∈ s then (e ⟨x, h⟩ : ℕ) else 0) ≤ j)
      = Finset.image (fun k : Fin s.card => ((e.symm k : ↥s) : α))
          (Finset.univ.filter fun k : Fin s.card => (k : ℕ) < j + 1) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hxs, hkx⟩ := hx
      refine Finset.mem_image.mpr ⟨e ⟨x, hxs⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [dif_pos hxs] at hkx; omega
      · simp
    · intro hx
      obtain ⟨k, hkm, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkm ⊢
      refine ⟨(e.symm k).2, ?_⟩
      rw [dif_pos (e.symm k).2]
      have h1 : (⟨↑(e.symm k), (e.symm k).2⟩ : ↥s) = e.symm k := rfl
      rw [h1, Equiv.apply_symm_apply]
      omega
  rw [himg, Finset.card_image_of_injective]
  · exact ejr_chain_two_voters_card_fin_filter_lt
  · intro k1 k2 h
    exact e.symm.injective (Subtype.ext h)

private lemma ejr_chain_two_voters_perm_of_rank {m : ℕ} (r : Fin m → ℕ) (hr : Function.Injective r) :
    ∃ σ : Equiv.Perm (Fin m), (∀ a b, r a < r b ↔ σ a < σ b) ∧
      (∀ a, (σ a : ℕ) = (Finset.univ.filter fun b => r b < r a).card) := by
  have key : ∀ a : Fin m, (Finset.univ.filter fun b : Fin m => r b < r a).card < m := by
    intro a
    have hne : (Finset.univ.filter fun b : Fin m => r b < r a) ≠ Finset.univ := by
      intro h
      have h2 : a ∈ Finset.univ.filter (fun b : Fin m => r b < r a) := by
        rw [h]; exact Finset.mem_univ a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
      exact lt_irrefl _ h2
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hne⟩)
    simpa using this
  set f : Fin m → Fin m := fun a => ⟨(Finset.univ.filter fun b => r b < r a).card, key a⟩ with hf
  have hmono : ∀ a b : Fin m, r a < r b →
      (Finset.univ.filter fun d => r d < r a).card < (Finset.univ.filter fun d => r d < r b).card := by
    intro a b hab
    have hne : (Finset.univ.filter fun d : Fin m => r d < r a) ≠
        (Finset.univ.filter fun d : Fin m => r d < r b) := by
      intro h
      have h2 : a ∈ Finset.univ.filter (fun d : Fin m => r d < r b) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hab
      rw [← h] at h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
      exact lt_irrefl _ h2
    have hss : (Finset.univ.filter fun d : Fin m => r d < r a) ⊂
        (Finset.univ.filter fun d : Fin m => r d < r b) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, hne⟩
      intro d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact Finset.card_lt_card hss
  have hfinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hval : (Finset.univ.filter fun d => r d < r a).card =
        (Finset.univ.filter fun d => r d < r b).card := by
      simpa [hf] using hab
    rcases lt_or_gt_of_ne (fun h => hne (hr h)) with h | h
    · have := hmono a b h; omega
    · have := hmono b a h; omega
  have hfbij : Function.Bijective f := ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  refine ⟨Equiv.ofBijective f hfbij, ?_, ?_⟩
  · intro a b
    constructor
    · intro h; exact hmono a b h
    · intro h
      have h' : f a < f b := by simpa using h
      rcases lt_trichotomy (r a) (r b) with h1 | h1 | h1
      · exact h1
      · have h2 : a = b := hr h1
        rw [h2] at h'
        exact absurd h' (lt_irrefl _)
      · exact absurd (hmono b a h1) (not_lt.mpr (le_of_lt h'))
  · intro a
    have h := Equiv.ofBijective_apply f hfbij a
    have h2 : ((Equiv.ofBijective f hfbij) a : ℕ) = (f a : ℕ) := by rw [h]
    rw [h2]

private lemma ejr_chain_two_voters_perm_exists {m : ℕ} (A : Fin 2 → Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m),
      (∀ c ∈ A 0 ∩ A 1, ∀ d, d ∉ A 0 ∩ A 1 → (σ c : ℕ) < (σ d : ℕ)) ∧
      (∀ (i : Fin 2) (c : Fin m), c ∈ A i →
        (σ c : ℕ) + 1 ≤ 2 * (Finset.univ.filter fun d => d ∈ A i ∧ (σ d : ℕ) ≤ (σ c : ℕ)).card) := by
  classical
  set C := A 0 ∩ A 1 with hC
  set R0 := A 0 \ A 1 with hR0
  set R1 := A 1 \ A 0 with hR1
  set N := Finset.univ \ (A 0 ∪ A 1) with hN
  have hCin : ∀ x : Fin m, x ∈ C ↔ x ∈ A 0 ∧ x ∈ A 1 := by
    intro x; rw [hC]; exact Finset.mem_inter
  have hR0in : ∀ x : Fin m, x ∈ R0 ↔ x ∈ A 0 ∧ x ∉ A 1 := by
    intro x; rw [hR0]; exact Finset.mem_sdiff
  have hR1in : ∀ x : Fin m, x ∈ R1 ↔ x ∈ A 1 ∧ x ∉ A 0 := by
    intro x; rw [hR1]; exact Finset.mem_sdiff
  have hcover : ∀ x : Fin m, x ∈ C ∨ x ∈ R0 ∨ x ∈ R1 ∨ x ∈ N := by
    intro x
    by_cases h0 : x ∈ A 0
    · by_cases h1 : x ∈ A 1
      · exact Or.inl ((hCin x).mpr ⟨h0, h1⟩)
      · exact Or.inr (Or.inl ((hR0in x).mpr ⟨h0, h1⟩))
    · by_cases h1 : x ∈ A 1
      · exact Or.inr (Or.inr (Or.inl ((hR1in x).mpr ⟨h1, h0⟩)))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hN]; simp [h0, h1]
  have dC0 : ∀ x, x ∈ C → x ∉ R0 := by
    intro x hx h; exact ((hR0in x).mp h).2 ((hCin x).mp hx).2
  have d0C : ∀ x, x ∈ R0 → x ∉ C := by
    intro x hx h; exact ((hR0in x).mp hx).2 ((hCin x).mp h).2
  have d1C : ∀ x, x ∈ R1 → x ∉ C := by
    intro x hx h; exact ((hR1in x).mp hx).2 ((hCin x).mp h).1
  have d01 : ∀ x, x ∈ R0 → x ∉ R1 := by
    intro x hx h; exact ((hR1in x).mp h).2 ((hR0in x).mp hx).1
  have memN : ∀ x, x ∉ C → x ∉ R0 → x ∉ R1 → x ∈ N := by
    intro x h1 h2 h3
    rcases hcover x with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  set kC : Fin m → ℕ := fun x => if h : x ∈ C then ((Finset.equivFin C ⟨x, h⟩ : Fin C.card) : ℕ) else 0 with hkC
  set k0 : Fin m → ℕ := fun x => if h : x ∈ R0 then ((Finset.equivFin R0 ⟨x, h⟩ : Fin R0.card) : ℕ) else 0 with hk0
  set k1 : Fin m → ℕ := fun x => if h : x ∈ R1 then ((Finset.equivFin R1 ⟨x, h⟩ : Fin R1.card) : ℕ) else 0 with hk1
  set kN : Fin m → ℕ := fun x => if h : x ∈ N then ((Finset.equivFin N ⟨x, h⟩ : Fin N.card) : ℕ) else 0 with hkN
  set r : Fin m → ℕ := fun x =>
    if x ∈ C then kC x
    else if x ∈ R0 then C.card + 2 * k0 x
    else if x ∈ R1 then C.card + 2 * k1 x + 1
    else C.card + 2 * R0.card + 2 * R1.card + kN x with hr
  have rC : ∀ x, x ∈ C → r x = kC x := by
    intro x h; rw [hr]; simp only [if_pos h]
  have rR0 : ∀ x, x ∉ C → x ∈ R0 → r x = C.card + 2 * k0 x := by
    intro x h h0; rw [hr]; simp only [if_neg h, if_pos h0]
  have rR1 : ∀ x, x ∉ C → x ∉ R0 → x ∈ R1 → r x = C.card + 2 * k1 x + 1 := by
    intro x h h0 h1; rw [hr]; simp only [if_neg h, if_neg h0, if_pos h1]
  have rN : ∀ x, x ∉ C → x ∉ R0 → x ∉ R1 → x ∈ N →
      r x = C.card + 2 * R0.card + 2 * R1.card + kN x := by
    intro x h h0 h1 hN'; rw [hr]; simp only [if_neg h, if_neg h0, if_neg h1]
  have kC_lt : ∀ x, x ∈ C → kC x < C.card := by
    intro x h; rw [hkC]; simp only [dif_pos h]; exact Fin.isLt _
  have k0_lt : ∀ x, x ∈ R0 → k0 x < R0.card := by
    intro x h; rw [hk0]; simp only [dif_pos h]; exact Fin.isLt _
  have k1_lt : ∀ x, x ∈ R1 → k1 x < R1.card := by
    intro x h; rw [hk1]; simp only [dif_pos h]; exact Fin.isLt _
  have kC_inj : ∀ x, x ∈ C → ∀ y, y ∈ C → kC x = kC y → x = y := by
    intro x hx y hy h
    rw [hkC] at h
    simp only [dif_pos hx, dif_pos hy] at h
    have h1 : (⟨x, hx⟩ : ↥C) = ⟨y, hy⟩ := (Finset.equivFin C).injective (Fin.ext h)
    exact Subtype.ext_iff.mp h1
  have k0_inj : ∀ x, x ∈ R0 → ∀ y, y ∈ R0 → k0 x = k0 y → x = y := by
    intro x hx y hy h
    rw [hk0] at h
    simp only [dif_pos hx, dif_pos hy] at h
    have h1 : (⟨x, hx⟩ : ↥R0) = ⟨y, hy⟩ := (Finset.equivFin R0).injective (Fin.ext h)
    exact Subtype.ext_iff.mp h1
  have k1_inj : ∀ x, x ∈ R1 → ∀ y, y ∈ R1 → k1 x = k1 y → x = y := by
    intro x hx y hy h
    rw [hk1] at h
    simp only [dif_pos hx, dif_pos hy] at h
    have h1 : (⟨x, hx⟩ : ↥R1) = ⟨y, hy⟩ := (Finset.equivFin R1).injective (Fin.ext h)
    exact Subtype.ext_iff.mp h1
  have kN_inj : ∀ x, x ∈ N → ∀ y, y ∈ N → kN x = kN y → x = y := by
    intro x hx y hy h
    rw [hkN] at h
    simp only [dif_pos hx, dif_pos hy] at h
    have h1 : (⟨x, hx⟩ : ↥N) = ⟨y, hy⟩ := (Finset.equivFin N).injective (Fin.ext h)
    exact Subtype.ext_iff.mp h1
  have hrinj : Function.Injective r := by
    intro x y hxy
    by_cases hxC : x ∈ C
    · have hxlt := kC_lt x hxC
      rw [rC x hxC] at hxy
      by_cases hyC : y ∈ C
      · rw [rC y hyC] at hxy; exact kC_inj x hxC y hyC hxy
      · by_cases hy0 : y ∈ R0
        · rw [rR0 y hyC hy0] at hxy; omega
        · by_cases hy1 : y ∈ R1
          · rw [rR1 y hyC hy0 hy1] at hxy; omega
          · rw [rN y hyC hy0 hy1 (memN y hyC hy0 hy1)] at hxy; omega
    · by_cases hx0 : x ∈ R0
      · have hxlt := k0_lt x hx0
        rw [rR0 x hxC hx0] at hxy
        by_cases hyC : y ∈ C
        · rw [rC y hyC] at hxy; have := kC_lt y hyC; omega
        · by_cases hy0 : y ∈ R0
          · rw [rR0 y hyC hy0] at hxy
            have hh : k0 x = k0 y := by omega
            exact k0_inj x hx0 y hy0 hh
          · by_cases hy1 : y ∈ R1
            · rw [rR1 y hyC hy0 hy1] at hxy; omega
            · rw [rN y hyC hy0 hy1 (memN y hyC hy0 hy1)] at hxy
              have := k0_lt x hx0; omega
      · by_cases hx1 : x ∈ R1
        · have hxlt := k1_lt x hx1
          rw [rR1 x hxC hx0 hx1] at hxy
          by_cases hyC : y ∈ C
          · rw [rC y hyC] at hxy; have := kC_lt y hyC; omega
          · by_cases hy0 : y ∈ R0
            · rw [rR0 y hyC hy0] at hxy; omega
            · by_cases hy1 : y ∈ R1
              · rw [rR1 y hyC hy0 hy1] at hxy
                have hh : k1 x = k1 y := by omega
                exact k1_inj x hx1 y hy1 hh
              · rw [rN y hyC hy0 hy1 (memN y hyC hy0 hy1)] at hxy
                have := k1_lt x hx1; omega
        · have hxN := memN x hxC hx0 hx1
          rw [rN x hxC hx0 hx1 hxN] at hxy
          by_cases hyC : y ∈ C
          · rw [rC y hyC] at hxy; have := kC_lt y hyC; omega
          · by_cases hy0 : y ∈ R0
            · rw [rR0 y hyC hy0] at hxy; have := k0_lt y hy0; omega
            · by_cases hy1 : y ∈ R1
              · rw [rR1 y hyC hy0 hy1] at hxy; have := k1_lt y hy1; omega
              · rw [rN y hyC hy0 hy1 (memN y hyC hy0 hy1)] at hxy
                have hh : kN x = kN y := by omega
                exact kN_inj x hxN y (memN y hyC hy0 hy1) hh
  obtain ⟨σ, hσlt, hσpos⟩ := ejr_chain_two_voters_perm_of_rank r hrinj
  refine ⟨σ, ?_, ?_⟩
  · intro c hc d hd
    have hcc : c ∈ C := hc
    have hdd : d ∉ C := hd
    have hrd : C.card ≤ r d := by
      by_cases hd0 : d ∈ R0
      · rw [rR0 d hdd hd0]; omega
      · by_cases hd1 : d ∈ R1
        · rw [rR1 d hdd hd0 hd1]; omega
        · rw [rN d hdd hd0 hd1 (memN d hdd hd0 hd1)]; omega
    have hlt : r c < r d := by
      rw [rC c hcc]
      have := kC_lt c hcc
      omega
    exact Fin.lt_def.mp ((hσlt c d).mp hlt)
  · intro i c hc
    have hσle : (σ c : ℕ) ≤ r c := by
      rw [hσpos c]
      have himg : (Finset.univ.filter fun d : Fin m => r d < r c).image r ⊆ Finset.range (r c) := by
        intro x hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact Finset.mem_range.mpr hd
      have h1 : (Finset.univ.filter fun d : Fin m => r d < r c).card
          = ((Finset.univ.filter fun d : Fin m => r d < r c).image r).card := by
        rw [Finset.card_image_of_injective _ hrinj]
      rw [h1]
      simpa using Finset.card_le_card himg
    have hiff : ∀ d : Fin m, ((σ d : ℕ) ≤ (σ c : ℕ)) ↔ (r d ≤ r c) := by
      intro d
      have h1 : ((σ d : ℕ) ≤ (σ c : ℕ)) ↔ (σ d ≤ σ c) := Fin.le_def.symm
      rw [h1]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact le_of_lt ((hσlt d c).mpr h')
        · have hdc : d = c := σ.injective h'
          rw [hdc]
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact le_of_lt (Fin.lt_def.mp ((hσlt d c).mp h'))
        · have hdc : d = c := hrinj h'
          rw [hdc]
    have hfilter : ∀ j : Fin 2, (Finset.univ.filter fun d => d ∈ A j ∧ (σ d : ℕ) ≤ (σ c : ℕ))
        = (Finset.univ.filter fun d => d ∈ A j ∧ r d ≤ r c) := by
      intro j
      apply Finset.filter_congr
      intro d _
      exact ⟨fun h => ⟨h.1, (hiff d).mp h.2⟩, fun h => ⟨h.1, (hiff d).mpr h.2⟩⟩
    have hCcase : ∀ (j : Fin 2), c ∈ C → c ∈ A j →
        (σ c : ℕ) + 1 ≤ 2 * (Finset.univ.filter fun d => d ∈ A j ∧ r d ≤ r c).card := by
      intro j hcc hcj
      have hmem : ∀ d, d ∈ C → d ∈ A j := by
        intro d hd
        fin_cases j
        · exact ((hCin d).mp hd).1
        · exact ((hCin d).mp hd).2
      have hsub : (Finset.univ.filter fun d => d ∈ C ∧ kC d ≤ kC c) ⊆
          (Finset.univ.filter fun d => d ∈ A j ∧ r d ≤ r c) := by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
        exact ⟨hmem d hd.1, by rw [rC d hd.1, rC c hcc]; exact hd.2⟩
      have hcard : (Finset.univ.filter fun d => d ∈ C ∧ kC d ≤ kC c).card = kC c + 1 := by
        rw [ejr_chain_two_voters_block_card C (Finset.equivFin C) kC hkC (kC c),
          min_eq_left (by have := kC_lt c hcc; omega)]
      have hlb : kC c + 1 ≤ (Finset.univ.filter fun d => d ∈ A j ∧ r d ≤ r c).card := by
        rw [← hcard]; exact Finset.card_le_card hsub
      have hrc : r c = kC c := rC c hcc
      omega
    have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    by_cases hcc : c ∈ C
    · rw [hfilter i]; exact hCcase i hcc hc
    · rcases hi01 with h | h
      · rw [h] at hc ⊢
        rw [hfilter 0]
        have hc0 : c ∈ R0 := (hR0in c).mpr ⟨hc, fun h1 => hcc ((hCin c).mpr ⟨hc, h1⟩)⟩
        have hrc : r c = C.card + 2 * k0 c := rR0 c hcc hc0
        have hdisj : Disjoint C R0 := Finset.disjoint_left.mpr (fun x hx hy => dC0 x hx hy)
        have hcardU : (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R0 ∧ k0 d ≤ k0 c)).card
            = C.card + (k0 c + 1) := by
          have h2 := ejr_chain_two_voters_filter_or_card C R0 (fun _ => True)
            (fun d => k0 d ≤ k0 c) hdisj
          rw [show (Finset.univ.filter fun d => (d ∈ C ∧ True) ∨ (d ∈ R0 ∧ k0 d ≤ k0 c))
                = (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R0 ∧ k0 d ≤ k0 c)) from by
              congr 1; ext d; simp] at h2
          rw [h2, Finset.filter_true_of_mem (s := C) (p := fun _ => True) (fun x _ => trivial),
              ← ejr_chain_two_voters_filter_mem_and R0 (fun d => k0 d ≤ k0 c),
              ejr_chain_two_voters_block_card R0 (Finset.equivFin R0) k0 hk0 (k0 c),
              min_eq_left (show k0 c + 1 ≤ R0.card by have := k0_lt c hc0; omega)]
        have hsub : (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R0 ∧ k0 d ≤ k0 c))
            ⊆ (Finset.univ.filter fun d => d ∈ A 0 ∧ r d ≤ r c) := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
          rcases hd with hd | hd
          · refine ⟨((hCin d).mp hd).1, ?_⟩
            rw [rC d hd, hrc]
            have := kC_lt d hd; omega
          · refine ⟨((hR0in d).mp hd.1).1, ?_⟩
            rw [rR0 d (d0C d hd.1) hd.1, hrc]
            have := hd.2; omega
        have hlb : C.card + (k0 c + 1)
            ≤ (Finset.univ.filter fun d => d ∈ A 0 ∧ r d ≤ r c).card := by
          rw [← hcardU]; exact Finset.card_le_card hsub
        omega
      · rw [h] at hc ⊢
        rw [hfilter 1]
        have hc1 : c ∈ R1 := (hR1in c).mpr ⟨hc, fun h1 => hcc ((hCin c).mpr ⟨h1, hc⟩)⟩
        have hc1' : c ∉ R0 := fun hh => d01 c hh hc1
        have hrc : r c = C.card + 2 * k1 c + 1 := rR1 c hcc hc1' hc1
        have hdisj : Disjoint C R1 := Finset.disjoint_left.mpr (fun x hx hy => d1C x hy hx)
        have hcardU : (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R1 ∧ k1 d ≤ k1 c)).card
            = C.card + (k1 c + 1) := by
          have h2 := ejr_chain_two_voters_filter_or_card C R1 (fun _ => True)
            (fun d => k1 d ≤ k1 c) hdisj
          rw [show (Finset.univ.filter fun d => (d ∈ C ∧ True) ∨ (d ∈ R1 ∧ k1 d ≤ k1 c))
                = (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R1 ∧ k1 d ≤ k1 c)) from by
              congr 1; ext d; simp] at h2
          rw [h2, Finset.filter_true_of_mem (s := C) (p := fun _ => True) (fun x _ => trivial),
              ← ejr_chain_two_voters_filter_mem_and R1 (fun d => k1 d ≤ k1 c),
              ejr_chain_two_voters_block_card R1 (Finset.equivFin R1) k1 hk1 (k1 c),
              min_eq_left (show k1 c + 1 ≤ R1.card by have := k1_lt c hc1; omega)]
        have hsub : (Finset.univ.filter fun d => (d ∈ C) ∨ (d ∈ R1 ∧ k1 d ≤ k1 c))
            ⊆ (Finset.univ.filter fun d => d ∈ A 1 ∧ r d ≤ r c) := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
          rcases hd with hd | hd
          · refine ⟨((hCin d).mp hd).2, ?_⟩
            rw [rC d hd, hrc]
            have := kC_lt d hd; omega
          · refine ⟨((hR1in d).mp hd.1).1, ?_⟩
            rw [rR1 d (d1C d hd.1) (fun hh => d01 d hh hd.1) hd.1, hrc]
            have := hd.2; omega
        have hlb : C.card + (k1 c + 1)
            ≤ (Finset.univ.filter fun d => d ∈ A 1 ∧ r d ≤ r c).card := by
          rw [← hcardU]; exact Finset.card_le_card hsub
        omega

private lemma ejr_chain_two_voters_level_supporters {m : ℕ} (A : Fin 2 → Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m → ∀ T : Finset (Fin m), T.Nonempty →
      (Finset.univ.filter fun i => T ⊆ A i ∧
        (A i ∩ Finset.univ.filter fun c => (σ c : ℕ) < k).card < T.card).card * k
      < T.card * 2 := by
  classical
  obtain ⟨σ, hseg, hspread⟩ := ejr_chain_two_voters_perm_exists A
  refine ⟨σ, ?_⟩
  have hcard : ∀ k ≤ m, (Finset.univ.filter fun c => (σ c : ℕ) < k).card = k :=
    fun k hk => ejr_chain_two_voters_prefix_card hk σ
  have hCeq : A 0 ∩ A 1 = Finset.univ.filter (fun c => (σ c : ℕ) < (A 0 ∩ A 1).card) := by
    set C := A 0 ∩ A 1 with hCdef
    have hCm : C.card ≤ m := by
      have h := Finset.card_le_univ C
      simpa using h
    have hsub : C ⊆ Finset.univ.filter (fun c => (σ c : ℕ) < C.card) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hge
      simp only [not_lt] at hge
      have hScard : (Finset.univ.filter (fun d => (σ d : ℕ) < (σ c : ℕ))).card = (σ c : ℕ) :=
        hcard (σ c) (le_of_lt (σ c).isLt)
      have hSC : (Finset.univ.filter (fun d => (σ d : ℕ) < (σ c : ℕ))) ⊆ C := by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        by_contra hdC
        have := hseg c hc d hdC
        omega
      have hne : (Finset.univ.filter (fun d => (σ d : ℕ) < (σ c : ℕ))) ≠ C := by
        intro h
        have hmem : c ∈ Finset.univ.filter (fun d => (σ d : ℕ) < (σ c : ℕ)) := h ▸ hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        omega
      have hlt : (Finset.univ.filter (fun d => (σ d : ℕ) < (σ c : ℕ))).card < C.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSC, hne⟩)
      omega
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard C.card hCm]
  have hCinter : ∀ k ≤ m, ((A 0 ∩ A 1) ∩ Finset.univ.filter (fun c => (σ c : ℕ) < k)).card
      = min k (A 0 ∩ A 1).card := by
    intro k hk
    rcases Nat.le_total k (A 0 ∩ A 1).card with h | h
    · have hsub : (Finset.univ.filter fun c => (σ c : ℕ) < k) ⊆ (A 0 ∩ A 1) := by
        rw [hCeq]
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        omega
      rw [Finset.inter_eq_right.mpr hsub, hcard k hk, min_eq_left h]
    · have hsub : (A 0 ∩ A 1) ⊆ (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
        rw [hCeq]
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        omega
      rw [Finset.inter_eq_left.mpr hsub, min_eq_right h]
  intro k hk T hT
  set W := Finset.univ.filter (fun c => (σ c : ℕ) < k) with hW
  set Sb := Finset.univ.filter (fun i : Fin 2 => T ⊆ A i ∧ (A i ∩ W).card < T.card) with hSb
  have hℓ : 0 < T.card := Finset.card_pos.mpr hT
  have hSb2 : Sb.card ≤ 2 := by
    have h := Finset.card_le_univ Sb
    simpa using h
  have hfactA : ∀ i : Fin 2, i ∈ Sb → k < 2 * T.card := by
    intro i hi
    rw [hSb, Finset.mem_filter] at hi
    obtain ⟨-, hiT, hicard⟩ := hi
    have hEne : (A i \ W).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_comm]
      have h1 : T.card ≤ (A i).card := Finset.card_le_card hiT
      omega
    obtain ⟨c, hcE, hcmin⟩ := Finset.exists_min_image (A i \ W) (fun d => (σ d : ℕ)) hEne
    rw [Finset.mem_sdiff] at hcE
    obtain ⟨hcA, hcW⟩ := hcE
    have hck : k ≤ (σ c : ℕ) := by
      rw [hW] at hcW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hcW
      exact hcW
    have hsub : (Finset.univ.filter fun d => d ∈ A i ∧ (σ d : ℕ) ≤ (σ c : ℕ))
        ⊆ (A i ∩ W) ∪ {c} := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      obtain ⟨hdA, hdle⟩ := hd
      by_cases hdW : d ∈ W
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hdA, hdW⟩)
      · have hdE : d ∈ A i \ W := Finset.mem_sdiff.mpr ⟨hdA, hdW⟩
        have h1 : (σ c : ℕ) ≤ (σ d : ℕ) := hcmin d hdE
        have h2 : (σ d : ℕ) = (σ c : ℕ) := le_antisymm hdle h1
        have h3 : d = c := σ.injective (Fin.ext h2)
        rw [h3]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self c)
    have hcardle : (Finset.univ.filter fun d => d ∈ A i ∧ (σ d : ℕ) ≤ (σ c : ℕ)).card
        ≤ (A i ∩ W).card + 1 := by
      calc (Finset.univ.filter fun d => d ∈ A i ∧ (σ d : ℕ) ≤ (σ c : ℕ)).card
          ≤ ((A i ∩ W) ∪ {c}).card := Finset.card_le_card hsub
        _ ≤ (A i ∩ W).card + ({c} : Finset (Fin m)).card := Finset.card_union_le _ _
        _ = (A i ∩ W).card + 1 := by rw [Finset.card_singleton]
    have hsp := hspread i c hcA
    omega
  have hfactB : (0 : Fin 2) ∈ Sb → (1 : Fin 2) ∈ Sb → k < T.card := by
    intro h0 h1
    rw [hSb, Finset.mem_filter] at h0 h1
    obtain ⟨-, hT0, hc0⟩ := h0
    obtain ⟨-, hT1, hc1⟩ := h1
    by_contra hcon
    simp only [not_lt] at hcon
    have hTC : T ⊆ A 0 ∩ A 1 := fun c hc => Finset.mem_inter.mpr ⟨hT0 hc, hT1 hc⟩
    have hCle : T.card ≤ (A 0 ∩ A 1).card := Finset.card_le_card hTC
    have h2 := hCinter k hk
    have hge : T.card ≤ (A 0 ∩ W).card := by
      have h3 : T.card ≤ ((A 0 ∩ A 1) ∩ W).card := by
        rw [h2]; exact le_min hcon hCle
      exact le_trans h3 (Finset.card_le_card (Finset.inter_subset_inter_right Finset.inter_subset_left))
    omega
  rcases Nat.lt_or_ge Sb.card 2 with h2 | h2
  · rcases Finset.eq_empty_or_nonempty Sb with he | hne
    · rw [he, Finset.card_empty, Nat.zero_mul]
      omega
    · obtain ⟨i, hi⟩ := hne
      have hAk := hfactA i hi
      have hone : Sb.card = 1 := by
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      rw [hone, Nat.one_mul]
      omega
  · have huniv : Sb = Finset.univ := by
      apply Finset.eq_univ_of_card
      have h := Finset.card_le_univ Sb
      have hc2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
      omega
    have h0 : (0 : Fin 2) ∈ Sb := by rw [huniv]; exact Finset.mem_univ _
    have h1 : (1 : Fin 2) ∈ Sb := by rw [huniv]; exact Finset.mem_univ _
    have hkℓ := hfactB h0 h1
    have hSbc : Sb.card = 2 := by rw [huniv]; simp
    rw [hSbc]
    omega

/-- The chain target holds for every profile with exactly two voters (verified by kernel decision for all profiles with m ≤ 4, and by exhaustive search for m ≤ 5; a general proof is not known). -/
theorem ejr_chain_two_voters {m : ℕ} (A : Fin 2 → Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := (ejr_chain_iff_level_supporters A).mpr (ejr_chain_two_voters_level_supporters A)
