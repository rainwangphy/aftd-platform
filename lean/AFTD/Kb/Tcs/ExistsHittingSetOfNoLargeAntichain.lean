import AFTD.Prelude

/-!
# exists_hitting_set_of_no_large_antichain

Topic: combinatorics   Node: f2751d3932c7

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

Let G be a finite family of nonempty subsets of a finite set α, w a natural number, and suppose every subfamily H ⊆ G that is an antichain (no two distinct members contained in one another) has at most w members. Then there is a set S ⊆ α with at most w elements meeting every member of G.
-/

/-- A family of nonempty finite sets with no antichain larger than w has a hitting set of size at most w, obtained by picking one element from each ⊆-minimal member. -/
theorem exists_hitting_set_of_no_large_antichain (α : Type*) [Fintype α] [DecidableEq α]
    (G : Finset (Finset α)) (w : ℕ) (hne : ∀ A ∈ G, A.Nonempty)
    (h : ∀ H : Finset (Finset α), H ⊆ G → (∀ A ∈ H, ∀ B ∈ H, A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A) → H.card ≤ w) :
    ∃ S : Finset α, S.card ≤ w ∧ ∀ A ∈ G, (A ∩ S).Nonempty := by
  classical
  let M : Finset (Finset α) := G.filter (fun A => ∀ B ∈ G, ¬ B ⊂ A)
  have hMsub : M ⊆ G := fun A hA => (Finset.mem_filter.mp hA).1
  have hex_min : ∀ A ∈ G, ∃ B ∈ M, B ⊆ A := by
    have key : ∀ n, ∀ A, A.card ≤ n → A ∈ G → ∃ B ∈ M, B ⊆ A := by
      intro n
      induction n with
      | zero =>
        intro A hcard hA
        exfalso
        have h0 : A.card = 0 := Nat.le_zero.mp hcard
        have hempty : A = ∅ := Finset.card_eq_zero.mp h0
        have hneA : A.Nonempty := hne A hA
        rw [hempty] at hneA
        exact Finset.not_nonempty_empty hneA
      | succ n ih =>
        intro A hcard hA
        by_cases hAM : A ∈ M
        · exact ⟨A, hAM, Finset.Subset.refl A⟩
        · have hnotmin : ¬ ∀ B ∈ G, ¬ B ⊂ A := by
            intro hc
            exact hAM (Finset.mem_filter.mpr ⟨hA, hc⟩)
          have hExists : ∃ B, B ∈ G ∧ B ⊂ A := by
            by_contra hc
            exact hnotmin (fun B hBG hBA => hc ⟨B, hBG, hBA⟩)
          obtain ⟨B, hBG, hBA⟩ := hExists
          have hlt : B.card < A.card := Finset.card_lt_card hBA
          have hle : B.card ≤ n := by omega
          obtain ⟨B', hB'M, hB'sub⟩ := ih B hle hBG
          exact ⟨B', hB'M, hB'sub.trans hBA.subset⟩
    intro A hA
    exact key A.card A le_rfl hA
  have hanti : ∀ A ∈ M, ∀ B ∈ M, A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A := by
    intro A hA B hB hAB
    obtain ⟨hAG, hAmin⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBG, hBmin⟩ := Finset.mem_filter.mp hB
    constructor
    · intro hsub
      exact hBmin A hAG ⟨hsub, fun hBA' => hAB (Finset.Subset.antisymm hsub hBA')⟩
    · intro hsub
      exact hAmin B hBG ⟨hsub, fun hAB' => hAB (Finset.Subset.antisymm hAB' hsub)⟩
  have hMcard : M.card ≤ w := h M hMsub hanti
  let x : (A : Finset α) → A ∈ M → α := fun A hA => Classical.choose (hne A (hMsub hA))
  have hx_mem : ∀ (A : Finset α) (hA : A ∈ M), x A hA ∈ A :=
    fun A hA => Classical.choose_spec (hne A (hMsub hA))
  let S : Finset α := M.attach.image (fun p => x p.1 p.2)
  have hScard : S.card ≤ w := by
    calc S.card ≤ M.attach.card := Finset.card_image_le
      _ = M.card := Finset.card_attach
      _ ≤ w := hMcard
  refine ⟨S, hScard, ?_⟩
  intro A hA
  obtain ⟨B, hBM, hBA⟩ := hex_min A hA
  have hxmem : x B hBM ∈ B := hx_mem B hBM
  have hxS : x B hBM ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨⟨B, hBM⟩, Finset.mem_attach M ⟨B, hBM⟩, rfl⟩
  exact ⟨x B hBM, Finset.mem_inter.mpr ⟨hBA hxmem, hxS⟩⟩
