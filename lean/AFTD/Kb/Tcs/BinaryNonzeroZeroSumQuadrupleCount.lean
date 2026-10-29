import AFTD.Prelude

/-!
# binary_nonzero_zero_sum_quadruple_count

Topic: graphs   Node: f76352422b3c

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

In any finite commutative exponent-two group with at least4 elements, the number of injective nonzero ordered4-tuples satisfying the stated zero-sum/common-nonzero-difference constraint equals the stated product of group-cardinality factors.
-/

private lemma bnsq_neg {G : Type*} [AddCommGroup G]
    (h2 : ∀ a : G, a + a = 0) : ∀ a : G, -a = a :=
  fun a => (eq_neg_of_add_eq_zero_left (h2 a)).symm

private lemma bnsq_sum_zero {G : Type*} [AddCommGroup G] (h2 : ∀ a : G, a + a = 0)
    {x y z w : G} (h : x + y + z + w = 0) : w = x + y + z := by
  have := eq_neg_of_add_eq_zero_right h
  rwa [bnsq_neg h2] at this

private lemma bnsq_inj {G : Type*} [AddCommGroup G] (h2 : ∀ a : G, a + a = 0)
    {x y z : G} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) (hzxy : z ≠ x + y) :
    Function.Injective (![x, y, z, x + y + z] : Fin 4 → G) := by
  have hneg : ∀ a : G, -a = a := bnsq_neg h2
  have hw0 : x + y + z ≠ 0 := by
    intro h
    exact hzxy (by rw [eq_neg_of_add_eq_zero_right h, hneg])
  have hwx : x + y + z ≠ x := by
    intro h
    apply hzy
    have h' : x + (y + z) = x + 0 := by simpa [add_assoc] using h
    have hsum : y + z = 0 := add_left_cancel h'
    exact ((eq_neg_of_add_eq_zero_left hsum).trans (hneg z)).symm
  have hwy : x + y + z ≠ y := by
    intro h
    apply hzx
    have h' : y + (x + z) = y + 0 := by
      calc y + (x + z) = x + y + z := by abel
        _ = y := h
        _ = y + 0 := by simp
    have hsum : x + z = 0 := add_left_cancel h'
    exact ((eq_neg_of_add_eq_zero_left hsum).trans (hneg z)).symm
  have hwz : x + y + z ≠ z := by
    intro h
    apply hyx
    have h' : z + (x + y) = z + 0 := by
      calc z + (x + y) = x + y + z := by abel
        _ = z := h
        _ = z + 0 := by simp
    have hsum : x + y = 0 := add_left_cancel h'
    exact ((eq_neg_of_add_eq_zero_left hsum).trans (hneg y)).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at hij ⊢
  all_goals first | rfl | tauto

private lemma bnsq_third {G : Type*} [AddCommGroup G] (h2 : ∀ a : G, a + a = 0)
    {f g : Fin 4 → G} (hf : (∑ i, f i) = 0) (hg : (∑ i, g i) = 0)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2' : f 2 = g 2) : f 3 = g 3 := by
  have hf3 : f 3 = f 0 + f 1 + f 2 :=
    bnsq_sum_zero h2 (by simpa [Fin.sum_univ_four] using hf)
  have hg3 : g 3 = g 0 + g 1 + g 2 :=
    bnsq_sum_zero h2 (by simpa [Fin.sum_univ_four] using hg)
  rw [hf3, hg3, h0, h1, h2']

theorem binary_nonzero_zero_sum_quadruple_count
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h2 : ∀ a : G, a + a = 0) (hcard : 4 ≤ Fintype.card G) :
    ((Finset.univ : Finset (Fin 4 → G)).filter (fun f =>
      Function.Injective f ∧ (∀ i, f i ≠ 0) ∧ ((∑ i, f i) = 0))).card =
      (Fintype.card G - 1) * (Fintype.card G - 2) * (Fintype.card G - 4) := by
  have hneg : ∀ a : G, -a = a := bnsq_neg h2
  let X : Finset G := (Finset.univ : Finset G).erase 0
  let Z : G → G → Finset G := fun x y => ((X.erase x).erase y).erase (x + y)
  let T : Finset ((x : G) × (y : G) × G) := X.sigma (fun x => (X.erase x).sigma (fun y => Z x y))
  let S : Finset (Fin 4 → G) := (Finset.univ : Finset (Fin 4 → G)).filter (fun f =>
      Function.Injective f ∧ (∀ i, f i ≠ 0) ∧ ((∑ i, f i) = 0))
  have hXmem : ∀ x : G, x ∈ X ↔ x ≠ 0 := by
    intro x; simp [X]
  have hXcard : X.card = Fintype.card G - 1 := by
    show ((Finset.univ : Finset G).erase 0).card = Fintype.card G - 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hZcard : ∀ x y : G, x ∈ X → y ∈ X.erase x → (Z x y).card = Fintype.card G - 4 := by
    intro x y hx hy
    have hx0 : x ≠ 0 := (hXmem x).mp hx
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyX : y ∈ X := (Finset.mem_erase.mp hy).2
    have hy0 : y ≠ 0 := (hXmem y).mp hyX
    have hxy0 : x + y ≠ 0 := by
      intro h
      exact hyx ((eq_neg_of_add_eq_zero_left h).trans (hneg y)).symm
    have hxplus_notx : x + y ≠ x := by
      intro h
      apply hy0
      exact add_left_cancel (a := x) (by simpa using h)
    have hxplus_noty : x + y ≠ y := by
      intro h
      apply hx0
      exact add_left_cancel (a := y) (by simpa [add_comm] using h)
    have hxplusX : x + y ∈ X := (hXmem _).mpr hxy0
    have hxplus_mem : x + y ∈ X.erase x := Finset.mem_erase.mpr ⟨hxplus_notx, hxplusX⟩
    have hxplusy_mem : x + y ∈ (X.erase x).erase y := Finset.mem_erase.mpr ⟨hxplus_noty, hxplus_mem⟩
    show (((X.erase x).erase y).erase (x + y)).card = Fintype.card G - 4
    rw [Finset.card_erase_of_mem hxplusy_mem, Finset.card_erase_of_mem hy,
      Finset.card_erase_of_mem hx, hXcard]
    omega
  have hTmem : ∀ x y z : G, (⟨x, y, z⟩ : (x : G) × (y : G) × G) ∈ T ↔
      x ≠ 0 ∧ y ≠ 0 ∧ y ≠ x ∧ z ≠ 0 ∧ z ≠ x ∧ z ≠ y ∧ z ≠ x + y := by
    intro x y z
    simp only [T, X, Z, Finset.mem_sigma, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have hSmem : ∀ f : Fin 4 → G, f ∈ S ↔
      Function.Injective f ∧ (∀ i, f i ≠ 0) ∧ ((∑ i, f i) = 0) := by
    intro f; simp [S]
  have hcardT : T.card = (Fintype.card G - 1) * (Fintype.card G - 2) * (Fintype.card G - 4) := by
    have hinner : ∀ x ∈ X, ((X.erase x).sigma (fun y => Z x y)).card =
        (Fintype.card G - 2) * (Fintype.card G - 4) := by
      intro x hx
      rw [Finset.card_sigma]
      have hsum : (∑ y ∈ X.erase x, (Z x y).card) =
          (X.erase x).card * (Fintype.card G - 4) := by
        apply Finset.sum_const_nat
        intro y hy
        exact hZcard x y hx hy
      rw [hsum]
      have hxcard : (X.erase x).card = Fintype.card G - 2 := by
        rw [Finset.card_erase_of_mem hx, hXcard]
        omega
      rw [hxcard]
    show (X.sigma (fun x => (X.erase x).sigma (fun y => Z x y))).card = _
    rw [Finset.card_sigma]
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_const_nat (m := (Fintype.card G - 2) * (Fintype.card G - 4))]
    · rw [hXcard]; ring
    · intro x hx; rfl
  have hST : S.card = T.card := by
    apply Finset.card_nbij (fun f : Fin 4 → G => (⟨f 0, f 1, f 2⟩ : (x : G) × (y : G) × G))
    · intro f hf
      rw [Finset.mem_coe, hSmem] at hf
      obtain ⟨hinj, hnz, hsum⟩ := hf
      show (⟨f 0, f 1, f 2⟩ : (x : G) × (y : G) × G) ∈ T
      rw [hTmem]
      have h3eq : f 3 = f 0 + f 1 + f 2 :=
        bnsq_sum_zero h2 (by simpa [Fin.sum_univ_four] using hsum)
      refine ⟨hnz 0, hnz 1, fun h => ?_, hnz 2, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · exact absurd (hinj h) (by decide)
      · exact absurd (hinj h) (by decide)
      · exact absurd (hinj h) (by decide)
      · apply hnz 3
        rw [h3eq, h]
        simpa using h2 (f 0 + f 1)
    · intro f hf g hg hfg
      rw [Finset.mem_coe, hSmem] at hf hg
      have h0 : f 0 = g 0 := congrArg Sigma.fst hfg
      have h1 : f 1 = g 1 := congrArg (fun t => t.2.1) hfg
      have h2' : f 2 = g 2 := congrArg (fun t => t.2.2) hfg
      have h3 : f 3 = g 3 := bnsq_third h2 hf.2.2 hg.2.2 h0 h1 h2'
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2'
      · exact h3
    · intro t ht
      simp only [Finset.mem_coe] at ht
      obtain ⟨x, y, z⟩ := t
      rw [hTmem] at ht
      obtain ⟨hx0, hy0, hyx, hz0, hzx, hzy, hzxy⟩ := ht
      show ∃ a : Fin 4 → G, a ∈ S ∧ (⟨a 0, a 1, a 2⟩ : (x : G) × (y : G) × G) = ⟨x, y, z⟩
      have hw0 : x + y + z ≠ 0 := by
        intro h
        exact hzxy (by rw [eq_neg_of_add_eq_zero_right h, hneg])
      refine ⟨![x, y, z, x + y + z], ?_, rfl⟩
      rw [hSmem]
      refine ⟨bnsq_inj h2 hyx hzx hzy hzxy, ?_, ?_⟩
      · intro i
        fin_cases i <;>
          simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
        all_goals first | exact hx0 | exact hy0 | exact hz0 | exact hw0
      · rw [Fin.sum_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three]
        exact h2 (x + y + z)
  rw [hST, hcardT]
