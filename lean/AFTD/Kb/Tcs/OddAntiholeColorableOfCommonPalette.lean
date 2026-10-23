import AFTD.Prelude
import AFTD.Kb.Tcs.G

/-!
# odd_antihole_colorable_of_common_palette

Topic: graphs   Node: ecc8c06015cb

Provenance: formalization of a published result. Source: arXiv:2610.14241 (Restricting odd antiholes in critical graphs via list coloring), Theorem 8, specialized to G = complement of C_{2ℓ-1} (whose complement, the odd cycle, is hypomatchable); partial result for OP-216 (the conjecture with the common-palette assumption)

Theorem 8 of arXiv:2610.14241 for the odd antihole: for ℓ ≥ 3, if all lists of an (ℓ-1)-assignment of complement(C_{2ℓ-1}) are subsets of a common ℓ-set P and are not all identical, then the antihole is L-colorable.
-/

open Fin.NatCast in
/-- Colouring from a system of distinct representatives of the classes
`{s + (2j-1), s + 2j}`, `j < ℓ` (class `0` is the singleton `{s}`). -/
theorem odd_antihole_colorable_of_common_palette_color (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    [NeZero (2 * ℓ - 1)] (L : Fin (2 * ℓ - 1) → Finset ℕ) (s : Fin (2 * ℓ - 1))
    (f : Fin ℓ → ℕ) (hf : Function.Injective f)
    (hft : ∀ j : Fin ℓ, f j ∈ L (s + ((2 * j.val - 1 : ℕ) : Fin (2 * ℓ - 1))) ∩
      L (s + ((2 * j.val : ℕ) : Fin (2 * ℓ - 1)))) :
    ∃ c : Fin (2 * ℓ - 1) → ℕ, (∀ v, c v ∈ L v) ∧
      ∀ u v, (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.Adj u v → c u ≠ c v := by
  have hcls : ∀ v : Fin (2 * ℓ - 1), ((v - s).val + 1) / 2 < ℓ := by
    intro v
    have := (v - s).isLt
    omega
  refine ⟨fun v => f ⟨((v - s).val + 1) / 2, hcls v⟩, ?_, ?_⟩
  · intro v
    have hv : s + (((v - s).val : ℕ) : Fin (2 * ℓ - 1)) = v := by
      rw [Fin.cast_val_eq_self]
      abel
    have h := hft ⟨((v - s).val + 1) / 2, hcls v⟩
    simp only [Finset.mem_inter] at h
    have key : 2 * (((v - s).val + 1) / 2) - 1 = (v - s).val ∨
        2 * (((v - s).val + 1) / 2) = (v - s).val := by omega
    rcases key with k | k
    · have h1 := h.1
      rw [k, hv] at h1
      exact h1
    · have h2 := h.2
      rw [k, hv] at h2
      exact h2
  · intro u v hadj heq
    rw [SimpleGraph.compl_adj] at hadj
    obtain ⟨hne, hnadj⟩ := hadj
    apply hnadj
    have heq' := Fin.mk.inj_iff.mp (hf heq)
    rw [SimpleGraph.cycleGraph_adj']
    have hij : (u - s).val ≠ (v - s).val := by
      intro h
      apply hne
      have : u - s = v - s := Fin.ext h
      simpa using this
    have hsub : u - v = (u - s) - (v - s) := by abel
    have hsub' : v - u = (v - s) - (u - s) := by abel
    rw [hsub, hsub']
    have hu := (u - s).isLt
    have hv := (v - s).isLt
    rcases (show (u - s).val = (v - s).val + 1 ∨ (v - s).val = (u - s).val + 1 by omega) with h | h
    · left
      rw [Fin.sub_def]
      simp only
      rw [h, show 2 * ℓ - 1 - (v - s).val + ((v - s).val + 1) = 1 + (2 * ℓ - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · right
      rw [Fin.sub_def]
      simp only
      rw [h, show 2 * ℓ - 1 - (u - s).val + ((u - s).val + 1) = 1 + (2 * ℓ - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Hall's condition for the classes of one pairing. -/
theorem odd_antihole_colorable_of_common_palette_hall (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (P : Finset ℕ)
    (hP : P.card = ℓ) (a b : ℕ → ℕ) (h0 : a 0 = b 0)
    (hA : ∃ k, 1 ≤ k ∧ k < ℓ ∧ a 0 ≠ a k ∧ a 0 ≠ b k)
    (hB : ∃ k₁ k₂, 1 ≤ k₁ ∧ k₁ < ℓ ∧ 1 ≤ k₂ ∧ k₂ < ℓ ∧
      (a k₁ = b k₁ ∨ (a k₂ ≠ a k₁ ∧ a k₂ ≠ b k₁) ∨ (b k₂ ≠ a k₁ ∧ b k₂ ≠ b k₁))) :
    ∃ f : Fin ℓ → ℕ, Function.Injective f ∧
      ∀ j : Fin ℓ, f j ∈ P.erase (a j.val) ∩ P.erase (b j.val) := by
  classical
  set t : Fin ℓ → Finset ℕ := fun j => P.erase (a j.val) ∩ P.erase (b j.val) with ht_def
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp
  have ht : ∀ j, ℓ - 2 ≤ (t j).card := by
    intro j
    have h1 : (P.erase (a j.val)).erase (b j.val) ⊆ t j := by
      intro x hx
      simp only [Finset.mem_erase] at hx
      simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
      tauto
    have h2 := Finset.pred_card_le_card_erase (s := P.erase (a j.val)) (a := b j.val)
    have h3 := Finset.pred_card_le_card_erase (s := P) (a := a j.val)
    have h4 := Finset.card_le_card h1
    omega
  have ht0 : ℓ - 1 ≤ (t ⟨0, by omega⟩).card := by
    have hsub : P.erase (a 0) ⊆ t ⟨0, by omega⟩ := by
      intro x hx
      simp only [ht_def, Finset.mem_inter]
      exact ⟨hx, by rw [← h0]; exact hx⟩
    have := Finset.card_le_card hsub
    have := Finset.pred_card_le_card_erase (s := P) (a := a 0)
    omega
  intro S
  have hSle : S.card ≤ ℓ := by simpa using Finset.card_le_univ S
  by_cases hS : S.card ≤ ℓ - 2
  · rcases S.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · simp
    · exact hS.trans ((ht j).trans (Finset.card_le_card (Finset.subset_biUnion_of_mem t hj)))
  by_cases h0S : (⟨0, by omega⟩ : Fin ℓ) ∈ S
  · by_cases hSf : S.card = ℓ
    · have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hSf)
      have hPsub : P ⊆ S.biUnion t := by
        intro x hx
        rw [Finset.mem_biUnion]
        by_cases hx0 : x = a 0
        · obtain ⟨k, hk1, hk2, hak, hbk⟩ := hA
          refine ⟨⟨k, hk2⟩, by rw [hSu]; exact Finset.mem_univ _, ?_⟩
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          rw [hx0] at hx ⊢
          exact ⟨⟨hak, hx⟩, ⟨hbk, hx⟩⟩
        · refine ⟨⟨0, by omega⟩, h0S, ?_⟩
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          exact ⟨⟨hx0, hx⟩, ⟨by rw [← h0]; exact hx0, hx⟩⟩
      calc S.card = ℓ := hSf
        _ = P.card := hP.symm
        _ ≤ _ := Finset.card_le_card hPsub
    · have : S.card ≤ ℓ - 1 := by omega
      exact this.trans (ht0.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem t h0S)))
  · obtain ⟨k₁, k₂, hk1, hk1', hk2, hk2', hcase⟩ := hB
    have hSsub : S ⊆ Finset.univ.erase ⟨0, by omega⟩ := by
      intro j hj
      rw [Finset.mem_erase]
      exact ⟨fun h => h0S (h ▸ hj), Finset.mem_univ _⟩
    have hSeq : S = Finset.univ.erase ⟨0, by omega⟩ := by
      apply Finset.eq_of_subset_of_card_le hSsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hm1 : (⟨k₁, hk1'⟩ : Fin ℓ) ∈ S := by
      rw [hSeq, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      simp only [Fin.ext_iff] at h
      omega
    have hm2 : (⟨k₂, hk2'⟩ : Fin ℓ) ∈ S := by
      rw [hSeq, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      simp only [Fin.ext_iff] at h
      omega
    have hsub1 := Finset.subset_biUnion_of_mem t hm1
    have hsub2 := Finset.subset_biUnion_of_mem t hm2
    have key : ∃ m, P.erase m ⊆ t ⟨k₁, hk1'⟩ ∪ t ⟨k₂, hk2'⟩ := by
      rcases hcase with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨a k₁, ?_⟩
        intro x hx
        apply Finset.mem_union_left
        simp only [Finset.mem_erase] at hx
        simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
        exact ⟨hx, ⟨by rw [← h]; exact hx.1, hx.2⟩⟩
      · refine ⟨b k₂, ?_⟩
        intro x hx
        simp only [Finset.mem_erase] at hx
        by_cases hxa : x = a k₂
        · apply Finset.mem_union_left
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          rw [hxa] at hx ⊢
          exact ⟨⟨h1, hx.2⟩, ⟨h2, hx.2⟩⟩
        · apply Finset.mem_union_right
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          exact ⟨⟨hxa, hx.2⟩, hx⟩
      · refine ⟨a k₂, ?_⟩
        intro x hx
        simp only [Finset.mem_erase] at hx
        by_cases hxb : x = b k₂
        · apply Finset.mem_union_left
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          rw [hxb] at hx ⊢
          exact ⟨⟨h1, hx.2⟩, ⟨h2, hx.2⟩⟩
        · apply Finset.mem_union_right
          simp only [ht_def, Finset.mem_inter, Finset.mem_erase]
          exact ⟨hx, ⟨hxb, hx.2⟩⟩
    obtain ⟨m, hm⟩ := key
    have hScard : S.card = ℓ - 1 := by
      rw [hSeq, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp only [Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_card (hm.trans (Finset.union_subset hsub1 hsub2))
    have := Finset.pred_card_le_card_erase (s := P) (a := m)
    omega

open Fin.NatCast in
/-- If every class of the pairing at `s` with index in `[lo, ℓ)` contains a vertex of
colour `c`, then at least `ℓ - lo` vertices have colour `c`. -/
theorem odd_antihole_colorable_of_common_palette_count (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    [NeZero (2 * ℓ - 1)] (μ : Fin (2 * ℓ - 1) → ℕ) (s : Fin (2 * ℓ - 1)) (c lo : ℕ)
    (h : ∀ k, lo ≤ k → k < ℓ → μ (s + ((2 * k - 1 : ℕ) : Fin (2 * ℓ - 1))) = c ∨
      μ (s + ((2 * k : ℕ) : Fin (2 * ℓ - 1))) = c) :
    ℓ - lo ≤ (Finset.univ.filter (fun v => μ v = c)).card := by
  have hw : ∀ i j : ℕ, i < 2 * ℓ - 1 → j < 2 * ℓ - 1 →
      s + ((i : ℕ) : Fin (2 * ℓ - 1)) = s + ((j : ℕ) : Fin (2 * ℓ - 1)) → i = j := by
    intro i j hi hj hij
    have h' := add_left_cancel hij
    have := congrArg Fin.val h'
    rwa [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt hj] at this
  let g : ℕ → Fin (2 * ℓ - 1) := fun k =>
    if μ (s + ((2 * k : ℕ) : Fin (2 * ℓ - 1))) = c then s + ((2 * k : ℕ) : Fin (2 * ℓ - 1))
    else s + ((2 * k - 1 : ℕ) : Fin (2 * ℓ - 1))
  have hle := Finset.card_le_card_of_injOn g (s := Finset.Ico lo ℓ)
    (t := Finset.univ.filter (fun v => μ v = c)) ?_ ?_
  · simpa using hle
  · intro k hk
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, g]
    split_ifs with h1
    · exact h1
    · exact (h k hk.1 hk.2).resolve_right h1
  · intro k1 hk1 k2 hk2 heq
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk1 hk2
    simp only [g] at heq
    split_ifs at heq <;> (have := hw _ _ (by omega) (by omega) heq; omega)

/-- Three distinct colour classes have at most `n` vertices together. -/
theorem odd_antihole_colorable_of_common_palette_sum3 {n : ℕ} (μ : Fin n → ℕ) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Finset.univ.filter (fun v => μ v = a)).card + (Finset.univ.filter (fun v => μ v = b)).card
      + (Finset.univ.filter (fun v => μ v = c)).card ≤ n := by
  have d1 : Disjoint (Finset.univ.filter (fun v => μ v = a))
      (Finset.univ.filter (fun v => μ v = b)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact hab (h1.symm.trans h2)
  have d2 : Disjoint (Finset.univ.filter (fun v => μ v = a) ∪
      Finset.univ.filter (fun v => μ v = b)) (Finset.univ.filter (fun v => μ v = c)) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      exact hac (h1.symm.trans h2)
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      exact hbc (h1.symm.trans h2)
  have e1 := Finset.card_union_of_disjoint d1
  have e2 := Finset.card_union_of_disjoint d2
  have e3 := Finset.card_le_univ (Finset.univ.filter (fun v => μ v = a) ∪
      Finset.univ.filter (fun v => μ v = b) ∪ Finset.univ.filter (fun v => μ v = c))
  rw [Fintype.card_fin] at e3
  omega

/-- Two distinct colour classes have at most `n` vertices together. -/
theorem odd_antihole_colorable_of_common_palette_sum2 {n : ℕ} (μ : Fin n → ℕ) (a b : ℕ)
    (hab : a ≠ b) :
    (Finset.univ.filter (fun v => μ v = a)).card +
      (Finset.univ.filter (fun v => μ v = b)).card ≤ n := by
  have d1 : Disjoint (Finset.univ.filter (fun v => μ v = a))
      (Finset.univ.filter (fun v => μ v = b)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact hab (h1.symm.trans h2)
  have e1 := Finset.card_union_of_disjoint d1
  have e3 := Finset.card_le_univ (Finset.univ.filter (fun v => μ v = a) ∪
      Finset.univ.filter (fun v => μ v = b))
  rw [Fintype.card_fin] at e3
  omega

theorem odd_antihole_colorable_of_common_palette (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (P : Finset ℕ)
    (hP : P.card = ℓ) (L : Fin (2 * ℓ - 1) → Finset ℕ) (hL : ∀ v, (L v).card = ℓ - 1)
    (hLP : ∀ v, L v ⊆ P) (hne : ∃ u v, L u ≠ L v) :
    ∃ c : Fin (2 * ℓ - 1) → ℕ, (∀ v, c v ∈ L v) ∧
      ∀ u v, (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.Adj u v → c u ≠ c v := by
  classical
  have : NeZero (2 * ℓ - 1) := ⟨by omega⟩
  letI : NatCast (Fin (2 * ℓ - 1)) := Fin.NatCast.instNatCast (2 * ℓ - 1)
  -- each list is the palette minus one colour `μ v`
  have hμ : ∀ v, ∃ m, m ∈ P ∧ L v = P.erase m := by
    intro v
    have hc : (P \ L v).card = 1 := by
      rw [Finset.card_sdiff_of_subset (hLP v), hP, hL]
      omega
    obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hc
    have hmP : m ∈ P ∧ m ∉ L v := by
      have : m ∈ P \ L v := by rw [hm]; exact Finset.mem_singleton_self m
      exact Finset.mem_sdiff.mp this
    refine ⟨m, hmP.1, ?_⟩
    ext x
    rw [Finset.mem_erase]
    constructor
    · intro hx
      exact ⟨fun h => hmP.2 (h ▸ hx), hLP v hx⟩
    · rintro ⟨hxm, hxP⟩
      by_contra hxL
      have : x ∈ P \ L v := Finset.mem_sdiff.mpr ⟨hxP, hxL⟩
      rw [hm, Finset.mem_singleton] at this
      exact hxm this
  choose μ _ hμL using hμ
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ c, F c = (Finset.univ.filter (fun v => μ v = c)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin (2 * ℓ - 1) → ℕ → ℕ,
      ∀ s k, A s k = μ (s + ((2 * k - 1 : ℕ) : Fin (2 * ℓ - 1))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin (2 * ℓ - 1) → ℕ → ℕ,
      ∀ s k, B s k = μ (s + ((2 * k : ℕ) : Fin (2 * ℓ - 1))) := ⟨_, fun _ _ => rfl⟩
  have hA0 : ∀ s, A s 0 = μ s := fun s => by rw [hA]; simp
  have hB0 : ∀ s, B s 0 = μ s := fun s => by rw [hB]; simp
  have hF1 : ∀ v, 1 ≤ F (μ v) := by
    intro v
    rw [hF]
    exact Finset.card_pos.mpr ⟨v, by simp⟩
  have hsum2 : ∀ a b, a ≠ b → F a + F b ≤ 2 * ℓ - 1 := by
    intro a b h
    rw [hF, hF]
    exact odd_antihole_colorable_of_common_palette_sum2 μ a b h
  have hsum3 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → F a + F b + F c ≤ 2 * ℓ - 1 := by
    intro a b c h1 h2 h3
    rw [hF, hF, hF]
    exact odd_antihole_colorable_of_common_palette_sum3 μ a b c h1 h2 h3
  have hcount : ∀ s c lo, (∀ k, lo ≤ k → k < ℓ → A s k = c ∨ B s k = c) → ℓ - lo ≤ F c := by
    intro s c lo h
    rw [hF]
    apply odd_antihole_colorable_of_common_palette_count ℓ hℓ μ s c lo
    intro k h1 h2
    rw [← hA, ← hB]
    exact h k h1 h2
  -- a pairing is good when Hall's condition holds for it
  let Good : Fin (2 * ℓ - 1) → Prop := fun s =>
    (∃ k, 1 ≤ k ∧ k < ℓ ∧ A s 0 ≠ A s k ∧ A s 0 ≠ B s k) ∧
    (∃ k₁ k₂, 1 ≤ k₁ ∧ k₁ < ℓ ∧ 1 ≤ k₂ ∧ k₂ < ℓ ∧
      (A s k₁ = B s k₁ ∨ (A s k₂ ≠ A s k₁ ∧ A s k₂ ≠ B s k₁) ∨
        (B s k₂ ≠ A s k₁ ∧ B s k₂ ≠ B s k₁)))
  have hmaj : ∀ s, ¬ Good s → ℓ ≤ F (μ s) ∨
      ∃ b, A s 1 ≠ b ∧ μ s ≠ A s 1 ∧ μ s ≠ b ∧ ℓ - 1 ≤ F (A s 1) ∧ ℓ - 1 ≤ F b := by
    intro s hng
    rw [not_and_or] at hng
    rcases hng with hnA | hnB
    · left
      have := hcount s (μ s) 0 (by
        intro k _ hk
        by_cases hk0 : k = 0
        · subst hk0
          left
          exact hA0 s
        · by_contra hcon
          push_neg at hcon
          exact hnA ⟨k, by omega, hk, by rw [hA0]; exact Ne.symm hcon.1,
            by rw [hA0]; exact Ne.symm hcon.2⟩)
      simpa using this
    · have hmix : ∀ k, 1 ≤ k → k < ℓ → A s k ≠ B s k :=
        fun k h1 h2 h => hnB ⟨k, 1, h1, h2, le_refl _, by omega, Or.inl h⟩
      have hinA : ∀ k, 1 ≤ k → k < ℓ → A s k = A s 1 ∨ A s k = B s 1 := by
        intro k h1 h2
        by_contra hc
        push_neg at hc
        exact hnB ⟨1, k, le_refl _, by omega, h1, h2, Or.inr (Or.inl hc)⟩
      have hinB : ∀ k, 1 ≤ k → k < ℓ → B s k = A s 1 ∨ B s k = B s 1 := by
        intro k h1 h2
        by_contra hc
        push_neg at hc
        exact hnB ⟨1, k, le_refl _, by omega, h1, h2, Or.inr (Or.inr hc)⟩
      have hcA : ∀ k, 1 ≤ k → k < ℓ → A s k = A s 1 ∨ B s k = A s 1 := by
        intro k h1 h2
        rcases hinA k h1 h2 with h | h
        · exact Or.inl h
        · rcases hinB k h1 h2 with h' | h'
          · exact Or.inr h'
          · exact absurd (h.trans h'.symm) (hmix k h1 h2)
      have hcB : ∀ k, 1 ≤ k → k < ℓ → A s k = B s 1 ∨ B s k = B s 1 := by
        intro k h1 h2
        rcases hinB k h1 h2 with h | h
        · rcases hinA k h1 h2 with h' | h'
          · exact absurd (h'.trans h.symm) (hmix k h1 h2)
          · exact Or.inl h'
        · exact Or.inr h
      have hFa := hcount s (A s 1) 1 hcA
      have hFb := hcount s (B s 1) 1 hcB
      by_cases hsa : μ s = A s 1
      · left
        have := hcount s (A s 1) 0 (by
          intro k _ hk
          by_cases hk0 : k = 0
          · subst hk0
            left
            rw [hA0]
            exact hsa
          · exact hcA k (by omega) hk)
        rw [hsa]
        simpa using this
      by_cases hsb : μ s = B s 1
      · left
        have := hcount s (B s 1) 0 (by
          intro k _ hk
          by_cases hk0 : k = 0
          · subst hk0
            right
            rw [hB0]
            exact hsb
          · exact hcB k (by omega) hk)
        rw [hsb]
        simpa using this
      right
      exact ⟨B s 1, hmix 1 le_rfl (by omega), hsa, hsb, hFa, hFb⟩
  have hgood : ∃ s, Good s := by
    by_contra hno
    have hno' : ∀ s, ¬ Good s := fun s hs => hno ⟨s, hs⟩
    obtain ⟨u, v, huv⟩ := hne
    have hμuv : μ u ≠ μ v := by
      intro h
      apply huv
      rw [hμL u, hμL v, h]
    obtain ⟨s, hs⟩ : ∃ s, F (μ s) < ℓ := by
      by_contra hc
      push_neg at hc
      have := hsum2 _ _ hμuv
      have := hc u
      have := hc v
      omega
    rcases hmaj s (hno' s) with h | ⟨b, hab, hsa, hsb, hFa, hFb⟩
    · omega
    · have hFa' : F (A s 1) < ℓ := by
        by_contra hc
        push_neg at hc
        have := hsum3 (μ s) (A s 1) b hsa hsb hab
        have := hF1 s
        omega
      obtain ⟨t, ht⟩ : ∃ t, t = s + ((2 * 1 - 1 : ℕ) : Fin (2 * ℓ - 1)) := ⟨_, rfl⟩
      have hAt : A s 1 = μ t := by rw [hA, ht]
      rcases hmaj t (hno' t) with h | ⟨b', hab', hta, htb, hFa'', hFb'⟩
      · rw [← hAt] at h
        omega
      · rw [← hAt] at hta htb
        have := hsum3 (A s 1) (A t 1) b' hta htb hab'
        omega
  obtain ⟨s, hsA, hsB⟩ := hgood
  obtain ⟨f, hf, hft⟩ := odd_antihole_colorable_of_common_palette_hall ℓ hℓ P hP (A s) (B s)
    (by rw [hA0, hB0]) hsA hsB
  apply odd_antihole_colorable_of_common_palette_color ℓ hℓ L s f hf
  intro j
  rw [hμL, hμL, ← hA, ← hB]
  exact hft j
