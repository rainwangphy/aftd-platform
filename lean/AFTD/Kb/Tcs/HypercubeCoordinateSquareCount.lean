import AFTD.Prelude

/-!
# hypercube_coordinate_square_count

Topic: graphs   Node: fbb0fbe464bc

Provenance: formalization of a published result. Source: arXiv:2611.27284 (The four-cycle extremal number of the seven-cube), Lemma 2.1, case k = 2 (number of coordinate 2-faces).

For n ≥ 2, the number of coordinate squares of the n-cube {0,1}^n is C(n,2)·2^(n-2), where a coordinate square is a vertex set of the form {u : u_k = v_k for all k ∉ {i, j}} for two distinct coordinates i ≠ j and a vertex v.
-/

theorem hcsq_card_zero_on (n : ℕ) (D : Finset (Fin n)) :
    (Finset.univ.filter fun w : Fin n → Bool => ∀ l ∈ D, w l = false).card = 2 ^ (n - D.card) := by
  classical
  rw [show n - D.card = (Dᶜ).card by rw [Finset.card_compl, Fintype.card_fin], ← Finset.card_powerset]
  refine Finset.card_bij' (fun w _ => Finset.univ.filter fun l => w l = true)
    (fun T _ => fun l => decide (l ∈ T)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.mem_powerset]
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.mem_compl]
    intro hlD
    rw [hw l hlD] at hl
    exact Bool.false_ne_true hl
  · intro T hT
    rw [Finset.mem_powerset] at hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro l hl
    simp only [decide_eq_false_iff_not]
    intro hlT
    exact Finset.mem_compl.1 (hT hlT) hl
  · intro w _
    funext l
    cases h : w l <;> simp [h]
  · intro T _
    ext l
    simp

open Classical in
theorem hypercube_coordinate_square_count (n : ℕ) (hn : 2 ≤ n) :
    (Finset.univ.filter fun s : Finset (Fin n → Bool) =>
      ∃ i j : Fin n, i ≠ j ∧ ∃ v : Fin n → Bool,
        s = Finset.univ.filter fun u => ∀ k, k ≠ i → k ≠ j → u k = v k).card =
      n.choose 2 * 2 ^ (n - 2) := by
  classical
  let I := (Finset.univ.powersetCard 2 : Finset (Finset (Fin n))).sigma fun D =>
    Finset.univ.filter fun w : Fin n → Bool => ∀ l ∈ D, w l = false
  let Φ : (Σ _ : Finset (Fin n), Fin n → Bool) → Finset (Fin n → Bool) := fun x =>
    Finset.univ.filter fun u => ∀ k, k ∉ x.1 → u k = x.2 k
  have hflip_mem : ∀ (D : Finset (Fin n)) (w : Fin n → Bool) (l : Fin n), l ∈ D →
      (fun k => if k = l then !w k else w k) ∈ Φ ⟨D, w⟩ := by
    intro D w l hl
    simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    have : k ≠ l := fun h => hk (h ▸ hl)
    simp [this]
  have hself : ∀ (D : Finset (Fin n)) (w : Fin n → Bool), w ∈ Φ ⟨D, w⟩ := by
    intro D w; simp [Φ]
  have hinj : Set.InjOn Φ I := by
    rintro ⟨D, w⟩ hx ⟨D', w'⟩ hy hxy
    simp only [Φ] at hxy
    rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
    have hw0 : ∀ l ∈ D, w l = false := by
      have := hx.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hw0' : ∀ l ∈ D', w' l = false := by
      have := hy.2; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hmem : ∀ u : Fin n → Bool, (∀ k, k ∉ D → u k = w k) ↔ (∀ k, k ∉ D' → u k = w' k) := by
      intro u
      have := Finset.ext_iff.1 hxy u
      simpa using this
    have hsub : ∀ {A B : Finset (Fin n)} {a b : Fin n → Bool},
        (∀ u : Fin n → Bool, (∀ k, k ∉ A → u k = a k) ↔ (∀ k, k ∉ B → u k = b k)) → A ⊆ B := by
      intro A B a b h l hlA
      by_contra hlB
      have h1 := (h a).1 (fun _ _ => rfl) l hlB
      have h2 := (h (fun k => if k = l then !a k else a k)).1 (by
        intro k hk
        have : k ≠ l := fun e => hk (e ▸ hlA)
        simp [this]) l hlB
      simp only [if_pos rfl] at h2
      rw [← h1] at h2
      cases a l <;> simp at h2
    have hDD : D = D' := Finset.Subset.antisymm (hsub hmem) (hsub (fun u => (hmem u).symm))
    subst hDD
    have hww : w = w' := by
      funext l
      by_cases hl : l ∈ D
      · rw [hw0 l hl, hw0' l hl]
      · exact (hmem w).1 (fun _ _ => rfl) l hl
    subst hww
    rfl
  have himage : (Finset.univ.filter fun s : Finset (Fin n → Bool) =>
      ∃ i j : Fin n, i ≠ j ∧ ∃ v : Fin n → Bool,
        s = Finset.univ.filter fun u => ∀ k, k ≠ i → k ≠ j → u k = v k) = I.image Φ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨i, j, hij, v, rfl⟩
      refine ⟨⟨{i, j}, fun k => if k ∈ ({i, j} : Finset (Fin n)) then false else v k⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma, Finset.mem_powersetCard]
        refine ⟨⟨Finset.subset_univ _, Finset.card_pair hij⟩, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro l hl; simp [hl]
      · ext u
        simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        constructor
        · intro h k hki hkj
          have := h k ⟨hki, hkj⟩
          simpa [hki, hkj] using this
        · rintro h k ⟨hki, hkj⟩
          simp [hki, hkj, h k hki hkj]
    · rintro ⟨⟨D, w⟩, hx, rfl⟩
      rw [Finset.mem_sigma, Finset.mem_powersetCard] at hx
      obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hx.1.2
      refine ⟨i, j, hij, w, ?_⟩
      ext u
      simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      constructor
      · intro h k hki hkj; exact h k ⟨hki, hkj⟩
      · rintro h k ⟨hki, hkj⟩; exact h k hki hkj
  rw [himage, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  rw [Finset.sum_congr rfl (fun D hD => by
    rw [hcsq_card_zero_on n D, (Finset.mem_powersetCard.1 hD).2])]
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
