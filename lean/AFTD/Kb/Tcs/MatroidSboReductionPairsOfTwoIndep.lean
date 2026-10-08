import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidStronglyBaseOrderable

/-!
# matroid_sbo_reduction_pairs_of_two_indep

Topic: combinatorics   Node: a26fa2ae6d5e

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Proposition 2.2. The classes are given as the orbits {e, p e} of an involution. The proof differs from the paper's: instead of applying strong base-orderability in the contraction by the common part of the two bases, the exchange bijection is made to fix that common part by successive transpositions, which keep the exchange property; disjointness of I and J is not used.

Let M be a finite strongly base-orderable matroid whose ground set is the union of two disjoint independent sets I and J. Then M has a reduction to a unit-capacity partition matroid with classes of size at most two: there is an involution p such that every subset T of the ground set containing no two distinct elements e, p e is independent in M.
-/

/-- One swap: composing an exchange bijection `φ : B₁ ≃ B₂` with the transposition of
`z = φ⁻¹(k)` and `k` (for `k ∈ B₁ ∩ B₂`) keeps the exchange property. -/
theorem sbo_exchange_swap {α : Type*} [DecidableEq α] (M : Matroid α) {B₁ B₂ : Set α} (φ : B₁ ≃ B₂)
    (hφ : ∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (φ x : α)) '' X)))
    (k : B₁) (hk : (k : α) ∈ B₂) (hne : (φ k : α) ≠ k) :
    ∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪
      ((fun x => (((Equiv.swap (φ.symm ⟨k, hk⟩) k).trans φ) x : α)) '' X)) := by
  classical
  intro X
  set z := φ.symm ⟨k, hk⟩ with hz
  have hφz : (φ z : α) = k := by simp [hz]
  have hzk : z ≠ k := fun h => hne (by rw [← h, hφz, h])
  have hsz : Equiv.swap z k z = k := Equiv.swap_apply_left z k
  have hsk : Equiv.swap z k k = z := Equiv.swap_apply_right z k
  have hso : ∀ x, x ≠ z → x ≠ k → Equiv.swap z k x = x :=
    fun x h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  have hkB : (k : α) ∈ B₁ := k.2
  have hcoe : ∀ x : B₁, (x : α) = k → x = k := fun x h => Subtype.ext h
  set Y : Set B₁ := if z ∈ X then insert k X else X \ {k} with hY
  convert hφ Y using 1
  ext a
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_image, Equiv.trans_apply]
  by_cases hzX : z ∈ X <;> by_cases hkX : k ∈ X
  · have hYX : Y = X := by rw [hY, if_pos hzX, Set.insert_eq_of_mem hkX]
    rw [hYX]
    have hmem : ∀ x ∈ X, Equiv.swap z k x ∈ X := by
      intro x hx
      by_cases h1 : x = z
      · rw [h1, hsz]; exact hkX
      by_cases h2 : x = k
      · rw [h2, hsk]; exact hzX
      rw [hso x h1 h2]; exact hx
    constructor
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Equiv.swap z k x, hmem x hx, rfl⟩
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Equiv.swap z k x, hmem x hx, by rw [Equiv.swap_apply_self]⟩
  · have hYX : Y = insert k X := by rw [hY, if_pos hzX]
    rw [hYX]
    constructor
    · rintro (⟨haB, ha⟩ | ⟨x, hx, rfl⟩)
      · by_cases hak : a = k
        · exact Or.inr ⟨z, Set.mem_insert_of_mem _ hzX, by rw [hφz, hak]⟩
        · refine Or.inl ⟨haB, ?_⟩
          rintro ⟨x, hx, rfl⟩
          rcases hx with rfl | hx
          · exact hak rfl
          · exact ha ⟨x, hx, rfl⟩
      · refine Or.inr ⟨Equiv.swap z k x, ?_, rfl⟩
        by_cases h1 : x = z
        · rw [h1, hsz]; exact Set.mem_insert _ _
        have h2 : x ≠ k := fun h => hkX (h ▸ hx)
        rw [hso x h1 h2]; exact Set.mem_insert_of_mem _ hx
    · rintro (⟨haB, ha⟩ | ⟨x, hx, rfl⟩)
      · exact Or.inl ⟨haB, fun ⟨x, hx, hxa⟩ => ha ⟨x, Set.mem_insert_of_mem _ hx, hxa⟩⟩
      · rcases hx with rfl | hx
        · exact Or.inr ⟨z, hzX, by rw [hsz]⟩
        · by_cases h1 : x = z
          · subst h1
            refine Or.inl ⟨by rw [hφz]; exact hkB, ?_⟩
            rintro ⟨y, hy, hya⟩
            rw [hφz] at hya
            exact hkX (hcoe y hya ▸ hy)
          · have h2 : x ≠ k := fun h => hkX (h ▸ hx)
            exact Or.inr ⟨x, hx, by rw [hso x h1 h2]⟩
  · have hYX : Y = X \ {k} := by rw [hY, if_neg hzX]
    rw [hYX]
    constructor
    · rintro (⟨haB, ha⟩ | ⟨x, hx, rfl⟩)
      · exact Or.inl ⟨haB, fun ⟨x, hx, hxa⟩ => ha ⟨x, hx.1, hxa⟩⟩
      · by_cases h2 : x = k
        · subst h2
          refine Or.inl ⟨by rw [hsk, hφz]; exact hkB, ?_⟩
          rintro ⟨y, hy, hya⟩
          rw [hsk, hφz] at hya
          exact hy.2 (hcoe y hya)
        · have h1 : x ≠ z := fun h => hzX (h ▸ hx)
          exact Or.inr ⟨x, ⟨hx, h2⟩, by rw [hso x h1 h2]⟩
    · rintro (⟨haB, ha⟩ | ⟨x, hx, rfl⟩)
      · by_cases hak : a = k
        · exact Or.inr ⟨k, hkX, by rw [hsk, hφz, hak]⟩
        · refine Or.inl ⟨haB, ?_⟩
          rintro ⟨x, hx, rfl⟩
          exact ha ⟨x, ⟨hx, fun h => hak (by rw [h])⟩, rfl⟩
      · have h1 : x ≠ z := fun h => hzX (h ▸ hx.1)
        exact Or.inr ⟨x, hx.1, by rw [hso x h1 hx.2]⟩
  · have hYX : Y = X := by rw [hY, if_neg hzX, Set.sdiff_singleton_eq_self hkX]
    rw [hYX]
    have hfix : ∀ x ∈ X, Equiv.swap z k x = x := fun x hx =>
      hso x (fun h => hzX (h ▸ hx)) (fun h => hkX (h ▸ hx))
    constructor
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, by rw [hfix x hx]⟩
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, by rw [hfix x hx]⟩

/-- In a matroid, an exchange bijection between two finite bases can be chosen to fix every
element the two bases share. -/
theorem sbo_exchange_fix_common {α : Type*} [DecidableEq α] (M : Matroid α) {B₁ B₂ : Set α} (hfin : B₁.Finite)
    (φ : B₁ ≃ B₂)
    (hφ : ∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (φ x : α)) '' X))) :
    ∃ ψ : B₁ ≃ B₂, (∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (ψ x : α)) '' X)))
      ∧ ∀ x : B₁, (x : α) ∈ B₂ → (ψ x : α) = x := by
  have : Finite B₁ := hfin.to_subtype
  suffices h : ∀ n : ℕ, ∀ φ : B₁ ≃ B₂,
      (∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (φ x : α)) '' X))) →
      {x : B₁ | (x : α) ∈ B₂ ∧ (φ x : α) ≠ x}.ncard ≤ n →
      ∃ ψ : B₁ ≃ B₂, (∀ X : Set B₁, M.IsBase ((B₁ \ ((↑) '' X)) ∪ ((fun x => (ψ x : α)) '' X)))
        ∧ ∀ x : B₁, (x : α) ∈ B₂ → (ψ x : α) = x from h _ φ hφ le_rfl
  intro n
  induction n with
  | zero =>
    intro φ hφ hn
    refine ⟨φ, hφ, fun x hx => ?_⟩
    by_contra h
    have : {x : B₁ | (x : α) ∈ B₂ ∧ (φ x : α) ≠ x}.Nonempty := ⟨x, hx, h⟩
    rw [← Set.ncard_pos (Set.toFinite _)] at this
    omega
  | succ n ih =>
    intro φ hφ hn
    by_cases hall : ∀ x : B₁, (x : α) ∈ B₂ → (φ x : α) = x
    · exact ⟨φ, hφ, hall⟩
    push Not at hall
    obtain ⟨k, hk, hne⟩ := hall
    set z := φ.symm ⟨k, hk⟩ with hz
    have hφz : (φ z : α) = k := by simp [hz]
    have hzk : z ≠ k := fun h => hne (by rw [← h, hφz, h])
    set φ' := (Equiv.swap z k).trans φ with hφ'
    apply ih φ' (sbo_exchange_swap M φ hφ k hk hne)
    have hsub : {x : B₁ | (x : α) ∈ B₂ ∧ (φ' x : α) ≠ x} ⊆
        {x : B₁ | (x : α) ∈ B₂ ∧ (φ x : α) ≠ x} \ {k} := by
      rintro x ⟨hx2, hxne⟩
      refine ⟨⟨hx2, ?_⟩, ?_⟩
      · by_cases h1 : x = z
        · rw [h1, hφz]; exact fun h => hzk (Subtype.ext h.symm)
        · by_cases h2 : x = k
          · subst h2; exact hne
          · rwa [hφ', Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2] at hxne
      · rintro rfl
        apply hxne
        rw [hφ', Equiv.trans_apply, Equiv.swap_apply_right, hφz]
    have hk' : k ∈ {x : B₁ | (x : α) ∈ B₂ ∧ (φ x : α) ≠ x} := ⟨hk, hne⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_sdiff_singleton_of_mem hk'] at this
    omega

theorem matroid_sbo_reduction_pairs_of_two_indep {α : Type*} (M : Matroid α) [M.Finite]
    (hM : matroid_strongly_base_orderable M) (I J : Set α) (hI : M.Indep I) (hJ : M.Indep J)
    (hIJ : Disjoint I J) (hE : I ∪ J = M.E) :
    ∃ p : α → α, Function.Involutive p ∧
      ∀ T ⊆ M.E, (∀ e ∈ T, p e ∈ T → p e = e) → M.Indep T := by
  classical
  obtain ⟨B₁, hB₁, hIB⟩ := hI.exists_isBase_superset
  obtain ⟨B₂, hB₂, hJB⟩ := hJ.exists_isBase_superset
  obtain ⟨φ₀, hφ₀⟩ := hM B₁ B₂ hB₁ hB₂
  obtain ⟨φ, hφ, hfix⟩ := sbo_exchange_fix_common M (M.ground_finite.subset hB₁.subset_ground)
    φ₀ hφ₀
  set p : α → α := fun a =>
    if h : a ∈ B₁ then (φ ⟨a, h⟩ : α) else if h2 : a ∈ B₂ then (φ.symm ⟨a, h2⟩ : α) else a
    with hp
  -- an element of `B₁ \ B₂` is sent outside `B₁`
  have hout : ∀ (a : α) (h : a ∈ B₁), a ∉ B₂ → (φ ⟨a, h⟩ : α) ∉ B₁ := by
    intro a h ha hb
    have h2 : (φ ⟨a, h⟩ : α) ∈ B₂ := (φ ⟨a, h⟩).2
    have := hfix ⟨_, hb⟩ h2
    have hinj : φ ⟨(φ ⟨a, h⟩ : α), hb⟩ = φ ⟨a, h⟩ := Subtype.ext this
    have := φ.injective hinj
    have h3 : (φ ⟨a, h⟩ : α) = a := congrArg Subtype.val this
    exact ha (h3 ▸ h2)
  refine ⟨p, ?_, ?_⟩
  · intro a
    by_cases h : a ∈ B₁
    · by_cases h2 : a ∈ B₂
      · have hf := hfix ⟨a, h⟩ h2
        simp only [hp, dif_pos h]
        simp only [hf, dif_pos h]
      · have hb := hout a h h2
        have hb2 : (φ ⟨a, h⟩ : α) ∈ B₂ := (φ ⟨a, h⟩).2
        simp only [hp, dif_pos h, dif_neg hb, dif_pos hb2]
        simp
    · by_cases h2 : a ∈ B₂
      · have hc : (φ.symm ⟨a, h2⟩ : α) ∈ B₁ := (φ.symm ⟨a, h2⟩).2
        simp only [hp, dif_neg h, dif_pos h2, dif_pos hc]
        simp
      · simp only [hp, dif_neg h, dif_neg h2]
  · intro T hT hTp
    set X : Set B₁ := {x | (φ x : α) ∈ T ∧ (x : α) ∉ B₂} with hX
    refine (hφ X).indep.subset ?_
    intro t ht
    by_cases htB : t ∈ B₁
    · refine Or.inl ⟨htB, ?_⟩
      rintro ⟨x, ⟨hxT, hxB⟩, rfl⟩
      have hpx : p x = (φ x : α) := by simp [hp, x.2]
      have := hTp x ht (hpx ▸ hxT)
      rw [hpx] at this
      exact hxB (this ▸ (φ x).2)
    · have htE : t ∈ I ∪ J := hE ▸ hT ht
      have htB2 : t ∈ B₂ := by
        rcases htE with h | h
        · exact absurd (hIB h) htB
        · exact hJB h
      set x := φ.symm ⟨t, htB2⟩ with hx
      have hφx : (φ x : α) = t := by simp [hx]
      have hxB : (x : α) ∉ B₂ := by
        intro h
        have := hfix x h
        rw [hφx] at this
        exact htB (this ▸ x.2)
      exact Or.inr ⟨x, ⟨hφx ▸ ht, hxB⟩, hφx⟩
