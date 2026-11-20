import AFTD.Prelude

/-!
# eight_vertex_nested_shore_endpoint_weight_bound

Topic: combinatorics   Node: b48ee133c82a

Provenance: helper lemma. Finite d=9 strict-interior bridge-shore step in the OP-1957 campaign.

Consider a family of four- and six-subsets of an eight-element set. Assign each a weight between one and two. If every pair of distinct members has union size at most six, intersection size at least four, and weights summing to at most two, then the total weight is at most two.
-/

theorem eight_vertex_nested_shore_endpoint_weight_bound
    (F : Finset (Finset (Fin 8))) (m : Finset (Fin 8) → ℕ)
    (hmember : ∀ W ∈ F, (W.card = 4 ∨ W.card = 6) ∧ 1 ≤ m W ∧ m W ≤ 2)
    (hpairs : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      (A ∪ B).card ≤ 6 ∧ 4 ≤ (A ∩ B).card ∧ m A + m B ≤ 2) :
    (∑ W ∈ F, m W) ≤ 2 := by
  classical
  have hinj : ∀ A ∈ F, ∀ B ∈ F, A.card = B.card → A = B := by
    intro A hA B hB hcard
    by_contra hne
    obtain ⟨hu, hi, hm⟩ := hpairs A hA B hB hne
    rcases (hmember A hA).1 with hA4 | hA6
    · have hI : (A ∩ B).card = A.card := by
        have hle := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
        omega
      have hIA : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hAB : A ⊆ B := by
        intro x hx
        have : x ∈ A ∩ B := by rwa [hIA]
        exact (Finset.mem_inter.mp this).2
      exact hne (Finset.eq_of_subset_of_card_le hAB (by omega))
    · have hUA : A ∪ B = A := by
        apply Eq.symm
        apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
        omega
      have hBA : B ⊆ A := by
        intro x hx
        have : x ∈ A ∪ B := Finset.mem_union.mpr (Or.inr hx)
        rwa [hUA] at this
      exact hne (Finset.eq_of_subset_of_card_le hBA (by omega)).symm
  have hF : F.card ≤ 2 := by
    have h := Finset.card_le_card_of_injOn (fun W : Finset (Fin 8) => W.card)
      (s := F) (t := ({4,6} : Finset ℕ))
      (by intro W hW; rcases (hmember W hW).1 with h | h <;> simp [h])
      (by intro A hA B hB h; exact hinj A hA B hB h)
    simpa using h
  by_cases hsmall : F.card ≤ 1
  · have hs : (∑ W ∈ F, m W) ≤ ∑ W ∈ F, (2 : ℕ) := by
      exact Finset.sum_le_sum (fun W hW => (hmember W hW).2.2)
    have hsum : (∑ W ∈ F, (2 : ℕ)) = F.card * 2 := by simp
    rw [hsum] at hs
    omega
  · obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    have hone : ∀ W ∈ F, m W = 1 := by
      intro W hW
      by_cases hWA : W = A
      · have hp := (hpairs W hW B hB (by simpa [hWA] using hAB)).2.2
        have hpos := (hmember B hB).2.1
        have hposW := (hmember W hW).2.1
        omega
      · have hp := (hpairs W hW A hA hWA).2.2
        have hpos := (hmember A hA).2.1
        have hposW := (hmember W hW).2.1
        omega
    have hsum : (∑ W ∈ F, m W) = F.card := by
      calc
        (∑ W ∈ F, m W) = ∑ W ∈ F, (1 : ℕ) := Finset.sum_congr rfl hone
        _ = F.card := by simp
    omega
