import AFTD.Prelude

/-!
# op861_middle_levels_strong_tail_exists

Topic: graphs   Node: 7681397ccf63

Provenance: helper lemma. Perfect matching between the equal middle layers of the Boolean lattice; the five-point case was checked in experiment 30755.

At the neighboring uniformity m=q+1, a single-tail hypergraph with strong q-domination exists on 2q+1 points.
-/

theorem op861_middle_levels_strong_tail_exists (q : ℕ) (hq : 1 ≤ q) :
    ∃ tail : Finset (Fin (2*q+1)) → Fin (2*q+1),
      (∀ E : Finset (Fin (2*q+1)), E.card = q+1 → tail E ∈ E) ∧
      (∀ R : Finset (Fin (2*q+1)), R.card = q → ∃ v, v ∉ R ∧ tail (insert v R) = v) := by
  classical
  set X : Finset (Finset (Fin (2*q+1))) := Finset.univ.powersetCard q with hX
  set Y : Finset (Finset (Fin (2*q+1))) := Finset.univ.powersetCard (q+1) with hY
  have memX : ∀ R : Finset (Fin (2*q+1)), R ∈ X ↔ R.card = q := by
    intro R; simp [hX]
  have memY : ∀ E : Finset (Fin (2*q+1)), E ∈ Y ↔ E.card = q+1 := by
    intro E; simp [hY]
  have card_sub_filter : ∀ (T : Finset (Finset (Fin (2*q+1)))) (p : Finset (Fin (2*q+1)) → Prop) [DecidablePred p],
      (Finset.univ.filter (fun R : ↥T => p (R : Finset (Fin (2*q+1))))).card = (T.filter p).card := by
    intro T p _
    have himg : (Finset.univ.filter (fun R : ↥T => p (R : Finset (Fin (2*q+1))))).image (Subtype.val) = T.filter p := by
      ext R
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨S, hS, rfl⟩
        exact ⟨S.2, hS⟩
      · rintro ⟨hT, hp⟩
        exact ⟨⟨R, hT⟩, hp, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
  have hUp : ∀ E : ↥Y, (Finset.univ.filter (fun R : ↥X => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).card = q+1 := by
    intro E
    rw [card_sub_filter X (fun R => R ⊆ (E : Finset (Fin (2*q+1))))]
    have hEq : X.filter (fun R : Finset (Fin (2*q+1)) => R ⊆ (E : Finset (Fin (2*q+1)))) = (E : Finset (Fin (2*q+1))).powersetCard q := by
      ext R
      rw [Finset.mem_filter, memX, Finset.mem_powersetCard]
      tauto
    rw [hEq, Finset.card_powersetCard, (memY _).mp E.2, Nat.choose_succ_self_right]
  have hDown : ∀ R : ↥X, (Finset.univ.filter (fun E : ↥Y => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).card ≤ q+1 := by
    intro R
    rw [card_sub_filter Y (fun E => (R : Finset (Fin (2*q+1))) ⊆ E)]
    have hRcard : (R : Finset (Fin (2*q+1))).card = q := (memX _).mp R.2
    have hmaps : Set.MapsTo (fun E : Finset (Fin (2*q+1)) => E \ (R : Finset (Fin (2*q+1))))
        ↑(Y.filter (fun E => (R : Finset (Fin (2*q+1))) ⊆ E))
        ↑((Finset.univ \ (R : Finset (Fin (2*q+1)))).powersetCard 1) := by
      intro E hE
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hE ⊢
      obtain ⟨hEY, hRE⟩ := hE
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hRE, (memY _).mp hEY, hRcard]
        omega
    have hinj : Set.InjOn (fun E : Finset (Fin (2*q+1)) => E \ (R : Finset (Fin (2*q+1))))
        ↑(Y.filter (fun E => (R : Finset (Fin (2*q+1))) ⊆ E)) := by
      intro E1 hE1 E2 hE2 h
      have h' : E1 \ (R : Finset (Fin (2*q+1))) = E2 \ (R : Finset (Fin (2*q+1))) := h
      simp only [Finset.mem_coe, Finset.mem_filter] at hE1 hE2
      rw [← Finset.union_sdiff_of_subset hE1.2, ← Finset.union_sdiff_of_subset hE2.2, h']
    calc (Y.filter (fun E => (R : Finset (Fin (2*q+1))) ⊆ E)).card
        ≤ ((Finset.univ \ (R : Finset (Fin (2*q+1)))).powersetCard 1).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = q+1 := by
            rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
              Finset.card_univ, Fintype.card_fin, hRcard, Nat.choose_one_right]
            omega
  have hall : ∀ A : Finset ↥Y,
      A.card ≤ (A.biUnion (fun E : ↥Y => Finset.univ.filter (fun R : ↥X => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1)))))).card := by
    intro A
    set N : Finset ↥X := A.biUnion (fun E : ↥Y => Finset.univ.filter (fun R : ↥X => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))) with hN
    set S : Finset (↥Y × ↥X) := (A ×ˢ Finset.univ).filter (fun p : ↥Y × ↥X => (p.2 : Finset (Fin (2*q+1))) ⊆ (p.1 : Finset (Fin (2*q+1)))) with hS
    have hS_mem : ∀ p : ↥Y × ↥X, p ∈ S ↔ p.1 ∈ A ∧ (p.2 : Finset (Fin (2*q+1))) ⊆ (p.1 : Finset (Fin (2*q+1))) := by
      intro p; simp [hS]
    have hS_fst : ∀ E ∈ A, (S.filter (fun p : ↥Y × ↥X => p.1 = E)).card = q+1 := by
      intro E hE
      have hfib : S.filter (fun p : ↥Y × ↥X => p.1 = E)
          = (Finset.univ.filter (fun R : ↥X => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).image (fun R => (E, R)) := by
        ext p
        rw [Finset.mem_filter, hS_mem, Finset.mem_image]
        constructor
        · rintro ⟨⟨hA, hsub⟩, hE1⟩
          exact ⟨p.2, by simpa [hE1] using hsub, by rw [← hE1]⟩
        · rintro ⟨R, hR, hp⟩
          rw [Finset.mem_filter] at hR
          rw [← hp]
          exact ⟨⟨hE, hR.2⟩, rfl⟩
      rw [hfib, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
      exact hUp E
    have hS_snd : ∀ R ∈ N, (S.filter (fun p : ↥Y × ↥X => p.2 = R)).card ≤ q+1 := by
      intro R _
      have hfib : S.filter (fun p : ↥Y × ↥X => p.2 = R)
          = (A.filter (fun E : ↥Y => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).image (fun E => (E, R)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, hS_mem]
        constructor
        · rintro ⟨⟨hA, hsub⟩, hR2⟩
          exact ⟨p.1, ⟨hA, by simpa [hR2] using hsub⟩, by rw [← hR2]⟩
        · rintro ⟨E, ⟨hA, hRE⟩, hp⟩
          rw [← hp]
          exact ⟨⟨hA, hRE⟩, rfl⟩
      rw [hfib, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
      calc (A.filter (fun E : ↥Y => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).card
          ≤ (Finset.univ.filter (fun E : ↥Y => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))))).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
        _ ≤ q+1 := hDown R
    have h1 : (q+1) * A.card ≤ S.card := by
      refine Finset.mul_card_image_le_card_of_maps_to (f := Prod.fst) (s := S) (t := A) ?_ (q+1) ?_
      · intro p hp
        exact (hS_mem p).mp hp |>.1
      · intro E hE
        exact (hS_fst E hE).ge
    have h2 : S.card ≤ (q+1) * N.card := by
      refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.snd) (s := S) (t := N) ?_ (q+1) ?_
      · intro p hp
        obtain ⟨hA, hsub⟩ := (hS_mem p).mp hp
        rw [hN]
        refine Finset.mem_biUnion.mpr ⟨p.1, hA, ?_⟩
        simpa using hsub
      · intro R hR
        exact hS_snd R hR
    exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) (by omega : 0 < q+1)
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun E : ↥Y => Finset.univ.filter (fun R : ↥X => (R : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1)))))).mp hall
  have hf_sub : ∀ E : ↥Y, (f E : Finset (Fin (2*q+1))) ⊆ (E : Finset (Fin (2*q+1))) := by
    intro E
    have h := hf_mem E
    simpa using h
  have hcardXY : Fintype.card ↥Y = Fintype.card ↥X := by
    rw [Fintype.card_coe, Fintype.card_coe]
    have hXc : X.card = Nat.choose (2*q+1) q := by
      rw [hX, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hYc : Y.card = Nat.choose (2*q+1) (q+1) := by
      rw [hY, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hXc, hYc]
    have hk : 2*q+1 - (q+1) = q := by omega
    have h := Nat.choose_symm (n := 2*q+1) (k := q+1) (by omega)
    rw [hk] at h
    exact h.symm
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcardXY⟩).2
  have hne : ∀ E : ↥Y, ((E : Finset (Fin (2*q+1))) \ (f E : Finset (Fin (2*q+1)))).Nonempty := by
    intro E
    have hsub := hf_sub E
    have hc : ((E : Finset (Fin (2*q+1))) \ (f E : Finset (Fin (2*q+1)))).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, (memY _).mp E.2, (memX _).mp (f E).2]
      omega
    exact Finset.card_pos.mp (by rw [hc]; norm_num)
  let tail : Finset (Fin (2*q+1)) → Fin (2*q+1) := fun E =>
    if h : E.card = q+1 then
      (E \ ((f ⟨E, (memY E).mpr h⟩ : ↥X) : Finset (Fin (2*q+1)))).min' (hne ⟨E, (memY E).mpr h⟩)
    else ⟨0, by omega⟩
  refine ⟨tail, ?_, ?_⟩
  · intro E hE
    have h1 : tail E = (E \ ((f ⟨E, (memY E).mpr hE⟩ : ↥X) : Finset (Fin (2*q+1)))).min' (hne ⟨E, (memY E).mpr hE⟩) := by
      simp only [tail]
      exact dif_pos hE
    rw [h1]
    exact (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).1
  · intro R hR
    have hRX : R ∈ X := (memX R).mpr hR
    obtain ⟨E, hE⟩ := hsurj ⟨R, hRX⟩
    have hcardE : (E : Finset (Fin (2*q+1))).card = q+1 := (memY _).mp E.2
    have hsub : R ⊆ (E : Finset (Fin (2*q+1))) := by
      have h1 := hf_sub E
      rw [hE] at h1
      simpa using h1
    set v : Fin (2*q+1) := ((E : Finset (Fin (2*q+1))) \ ((f ⟨(E : Finset (Fin (2*q+1))), (memY _).mpr hcardE⟩ : ↥X) : Finset (Fin (2*q+1)))).min' (hne ⟨(E : Finset (Fin (2*q+1))), (memY _).mpr hcardE⟩) with hv
    have hfE : f ⟨(E : Finset (Fin (2*q+1))), (memY _).mpr hcardE⟩ = ⟨R, hRX⟩ := by
      rw [show (⟨(E : Finset (Fin (2*q+1))), (memY _).mpr hcardE⟩ : ↥Y) = E from Subtype.ext rfl, hE]
    have hvmem : v ∈ (E : Finset (Fin (2*q+1))) \ ((f ⟨(E : Finset (Fin (2*q+1))), (memY _).mpr hcardE⟩ : ↥X) : Finset (Fin (2*q+1))) :=
      Finset.min'_mem _ _
    have hvR : v ∉ R := by
      have h2 := (Finset.mem_sdiff.mp hvmem).2
      rw [hfE] at h2
      exact h2
    have hvE : v ∈ (E : Finset (Fin (2*q+1))) := (Finset.mem_sdiff.mp hvmem).1
    have hins : insert v R = (E : Finset (Fin (2*q+1))) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hvE
        · exact hsub hx
      · rw [hcardE, Finset.card_insert_of_notMem hvR, hR]
    refine ⟨v, hvR, ?_⟩
    rw [hins]
    have htv : tail (E : Finset (Fin (2*q+1))) = v := by
      simp only [tail]
      exact dif_pos hcardE
    exact htv
