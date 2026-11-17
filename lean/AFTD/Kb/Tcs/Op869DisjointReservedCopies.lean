import AFTD.Prelude

/-!
# op869_disjoint_reserved_copies

Topic: online_algorithms   Node: 33c1f4de8b38

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.5: reserve disjoint bipartite copies and orient them for an offline three-coloring.

If each of q colors occurs in at least qD copies, one can reserve D copies for each color so that reservations for different colors are disjoint.
-/

theorem op869_disjoint_reserved_copies {α : Type} [DecidableEq α] (q D : ℕ) (S : Fin q → Finset α) :
    (∀ i, q * D ≤ (S i).card) →
    ∃ T : Fin q → Finset α, (∀ i, T i ⊆ S i ∧ (T i).card = D) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) := by
  classical
  intro hS
  have hHall : ∀ A : Finset (Fin q × Fin D), A.card ≤ (A.biUnion (fun p => S p.1)).card := by
    intro A
    by_cases hA : A.Nonempty
    · obtain ⟨⟨i, d⟩, hid⟩ := hA
      calc
        A.card ≤ Fintype.card (Fin q × Fin D) := Finset.card_le_univ A
        _ = q * D := by simp
        _ ≤ (S i).card := hS i
        _ ≤ (A.biUnion (fun p => S p.1)).card :=
          Finset.card_le_card (Finset.subset_biUnion_of_mem (fun p => S p.1) hid)
    · have hA' : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [hA']
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective (fun p : Fin q × Fin D => S p.1)).mp hHall
  let T : Fin q → Finset α := fun i => Finset.univ.image (fun d : Fin D => f (i, d))
  refine ⟨T, ?_, ?_⟩
  · intro i
    constructor
    · intro a ha
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
      exact hmem (i,d)
    · have hinj : Function.Injective (fun d : Fin D => f (i,d)) := by
        intro a b hab
        exact congrArg Prod.snd (hf hab)
      simp [T, Finset.card_image_of_injective _ hinj]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨d, hd, hda⟩ := Finset.mem_image.mp hai
    obtain ⟨e, he, hea⟩ := Finset.mem_image.mp haj
    have heq : (i, d) = (j, e) := hf (hda.trans hea.symm)
    exact hij (congrArg Prod.fst heq)
