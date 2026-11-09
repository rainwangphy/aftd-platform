import AFTD.Prelude

/-!
# finite_family_injective_representatives_avoiding

Topic: combinatorics   Node: 75b34226b84f

Provenance: helper lemma. A direct consequence of the finite matching theorem, used in the triangle-packing representative kernel.

For a finite indexed family of finite sets and a finite forbidden set, if every member contains at least as many elements as the number of indices plus the size of the forbidden set, there is an injective choice of representatives outside the forbidden set.
-/

theorem finite_family_injective_representatives_avoiding
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (B : Finset α)
    (hlarge : ∀ i, Fintype.card ι + B.card ≤ (A i).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ A i ∧ f i ∉ B := by
  classical
  have hhall : ∀ s : Finset ι, s.card ≤ (s.biUnion fun i => A i \ B).card := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      have hsub : A i \ B ⊆ s.biUnion (fun j => A j \ B) :=
        Finset.subset_biUnion_of_mem (fun j : ι => A j \ B) hi
      have h₁ := Finset.card_le_card hsub
      have h₂ := Finset.card_le_univ s
      have h₃ := Finset.card_le_card_sdiff_add_card (s := A i) (t := B)
      have h₄ := hlarge i
      omega
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [this]
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun i => A i \ B)).mp hhall
  exact ⟨f, hfinj, fun i => Finset.mem_sdiff.mp (hf i)⟩
