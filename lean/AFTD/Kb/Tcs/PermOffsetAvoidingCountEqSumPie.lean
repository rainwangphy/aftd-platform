import AFTD.Prelude
import AFTD.Kb.Tcs.PermOffsetAvoidingCount
import AFTD.Kb.Tcs.PermOffsetRookNumber

/-!
# perm_offset_avoiding_count_eq_sum_pie

Topic: combinatorics   Node: 2a2d77d575ba

Provenance: formalization of a published result. Source: arXiv:2610.23958 Equation (2)

For every natural number n and finite subset S ⊆ ℤ, the integer count (perm_offset_avoiding_count n S : ℤ) of S-avoiding permutations equals the sum over k from 0 to n of (-1 : ℤ) ^ k * ((n - k).factorial : ℤ) * (perm_offset_rook_number n S k : ℤ).
-/

open Classical in
theorem perm_offset_avoiding_count_eq_sum_pie_extend_card (n : ℕ) (T : Finset (Fin n × Fin n))
    (hT : ∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → c1.1 ≠ c2.1 ∧ c1.2 ≠ c2.2) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ c ∈ T, π c.1 = c.2)).card
      = (n - T.card).factorial := by
  set A := T.image Prod.fst with hA
  set B := T.image Prod.snd with hB
  have hAcard : A.card = T.card := by
    apply Finset.card_image_of_injOn
    intro c1 h1 c2 h2 h
    by_contra hne
    exact (hT c1 h1 c2 h2 hne).1 h
  let f : Fin n → Fin n := fun a => if h : ∃ b, (a, b) ∈ T then h.choose else a
  have hf : ∀ a b, (a, b) ∈ T → f a = b := by
    intro a b hab
    have h : ∃ b, (a, b) ∈ T := ⟨b, hab⟩
    simp only [f, dif_pos h]
    by_contra hne
    exact (hT _ h.choose_spec _ hab (by simp [hne])).1 rfl
  have hfA : ∀ x ∈ A, (x, f x) ∈ T := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    rw [hf c.1 c.2 hc]; exact hc
  let e : {x // x ∈ A} ≃ {y // y ∈ B} := Equiv.ofBijective
    (fun x => ⟨f x.1, Finset.mem_image.mpr ⟨_, hfA x.1 x.2, rfl⟩⟩) (by
      constructor
      · rintro ⟨x1, h1⟩ ⟨x2, h2⟩ h
        simp only [Subtype.mk.injEq] at h
        apply Subtype.ext
        by_contra hne
        exact (hT _ (hfA x1 h1) _ (hfA x2 h2) (by simp [hne])).2 h
      · rintro ⟨y, hy⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨⟨c.1, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩, Subtype.ext (hf _ _ hc)⟩)
  let τ : Equiv.Perm (Fin n) := e.extendSubtype
  have hτ : ∀ c ∈ T, τ c.1 = c.2 := by
    intro c hc
    have hm : c.1 ∈ A := Finset.mem_image.mpr ⟨c, hc, rfl⟩
    simp only [τ]
    rw [Equiv.extendSubtype_apply_of_mem e c.1 hm]
    exact hf _ _ hc
  rw [← Fintype.card_subtype]
  have key : {π : Equiv.Perm (Fin n) // ∀ c ∈ T, π c.1 = c.2} ≃
      {σ : Equiv.Perm (Fin n) // ∀ a, ¬ (a ∉ A) → σ a = a} :=
    { toFun := fun π => ⟨τ⁻¹ * π.1, by
        intro a ha
        have ha' : a ∈ A := not_not.mp ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha'
        rw [Equiv.Perm.mul_apply, π.2 c hc, ← hτ c hc]
        simp⟩
      invFun := fun σ => ⟨τ * σ.1, by
        intro c hc
        have hm : c.1 ∈ A := Finset.mem_image.mpr ⟨c, hc, rfl⟩
        rw [Equiv.Perm.mul_apply, σ.2 c.1 (by simpa using hm), hτ c hc]⟩
      left_inv := fun π => by ext; simp
      right_inv := fun σ => by ext; simp }
  rw [Fintype.card_congr key, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm _),
    Fintype.card_perm, Fintype.card_subtype, ← hAcard]
  congr 1
  rw [show (Finset.univ.filter fun x => x ∉ A) = Aᶜ by ext; simp, Finset.card_compl,
    Fintype.card_fin]

/-- Principle of inclusion-exclusion expansion of the avoiding count in terms of the rook numbers. -/
theorem perm_offset_avoiding_count_eq_sum_pie (n : ℕ) (S : Finset ℤ) :
    (perm_offset_avoiding_count n S : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n - k).factorial : ℤ) * (perm_offset_rook_number n S k : ℤ) := by
  classical
  set X : Finset (Fin n × Fin n) := Finset.univ.filter
    (fun c => ∃ s ∈ S, (n : ℤ) ∣ ((c.2 : ℕ) : ℤ) - ((c.1 : ℕ) : ℤ) - s) with hX
  have hA : perm_offset_avoiding_count n S = (Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => X.filter (fun c => π c.1 = c.2) = ∅)).card := by
    unfold perm_offset_avoiding_count
    congr 1
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.filter_eq_empty_iff, X]
    constructor
    · rintro h c ⟨s, hs, hd⟩ heq
      apply h c.1 s hs
      rw [heq]; exact hd
    · intro h i s hs hd
      exact @h (i, π i) ⟨s, hs, hd⟩ rfl
  have hB : ((Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => X.filter (fun c => π c.1 = c.2) = ∅)).card : ℤ) =
      ∑ T ∈ X.powerset, (-1 : ℤ) ^ T.card *
        ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ c ∈ T, π c.1 = c.2)).card : ℤ) := by
    calc _ = ∑ π : Equiv.Perm (Fin n), ∑ T ∈ (X.filter (fun c => π c.1 = c.2)).powerset,
          (-1 : ℤ) ^ T.card := by
          rw [Finset.natCast_card_filter]
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [Finset.sum_powerset_neg_one_pow_card]
      _ = ∑ π : Equiv.Perm (Fin n), ∑ T ∈ X.powerset,
          if (∀ c ∈ T, π c.1 = c.2) then (-1 : ℤ) ^ T.card else 0 := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext T
          simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
          constructor
          · intro h; exact ⟨fun c hc => (h hc).1, fun c hc => (h hc).2⟩
          · rintro ⟨h1, h2⟩ c hc; exact ⟨h1 hc, h2 c hc⟩
      _ = ∑ T ∈ X.powerset, ∑ π : Equiv.Perm (Fin n),
          if (∀ c ∈ T, π c.1 = c.2) then (-1 : ℤ) ^ T.card else 0 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.natCast_card_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun π _ => ?_
          split_ifs <;> simp
  have hC : ∀ T ∈ X.powerset, (-1 : ℤ) ^ T.card *
      ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ c ∈ T, π c.1 = c.2)).card : ℤ) =
      if (∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → c1.1 ≠ c2.1 ∧ c1.2 ≠ c2.2)
      then (-1 : ℤ) ^ T.card * ((n - T.card).factorial : ℤ) else 0 := by
    intro T _
    split_ifs with hP
    · rw [perm_offset_avoiding_count_eq_sum_pie_extend_card n T hP]
    · have hE : Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ c ∈ T, π c.1 = c.2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro π _ hπ
        apply hP
        intro c1 h1 c2 h2 hne
        have e1 := hπ c1 h1
        have e2 := hπ c2 h2
        constructor
        · intro h
          apply hne
          refine Prod.ext h ?_
          rw [← e1, ← e2, h]
        · intro h
          apply hne
          have h' : c1.1 = c2.1 := π.injective (by rw [e1, e2, h])
          exact Prod.ext h' h
      rw [hE]; simp
  rw [hA, hB, Finset.sum_congr rfl hC, ← Finset.sum_filter]
  have hmaps : ∀ T ∈ X.powerset.filter
      (fun T => ∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → c1.1 ≠ c2.1 ∧ c1.2 ≠ c2.2),
      T.card ∈ Finset.range (n + 1) := by
    intro T hT
    have hP := (Finset.mem_filter.mp hT).2
    have h1 : (T.image Prod.fst).card = T.card := by
      apply Finset.card_image_of_injOn
      intro c1 h1 c2 h2 h
      by_contra hne
      exact (hP c1 h1 c2 h2 hne).1 h
    have h2 : (T.image Prod.fst).card ≤ n := by
      simpa using Finset.card_le_univ (T.image Prod.fst)
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2]),
    Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  try simp only [Nat.cast_inj]
  unfold perm_offset_rook_number
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard, X]
  tauto
