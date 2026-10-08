import AFTD.Prelude

/-!
# card_piFinset_filter_apply_mem

Topic: algebraic_complexity   Node: e73112de24be

Provenance: helper lemma. folklore

For any type α with decidable equality, any positive integer n, any finite subset S of α, any subset T of α with T ⊆ S, and any coordinate index i₀ : Fin n, the cardinality of the set of points in the product S^n whose i₀-th coordinate belongs to T equals T.card * S.card ^ (n - 1).
-/

/-- The number of points in S^n whose i₀-th coordinate belongs to a subset T ⊆ S equals |T| * |S|^(n-1). -/
theorem card_piFinset_filter_apply_mem {α : Type*} [DecidableEq α] {n : ℕ} (hn : 0 < n)
    (S : Finset α) (T : Finset α) (hT : T ⊆ S) (i₀ : Fin n) :
    Finset.card (Finset.filter (fun x => x i₀ ∈ T) (Fintype.piFinset (fun _ : Fin n => S))) =
      T.card * S.card ^ (n - 1) := by
  have _ := hn
  have h_set : Finset.filter (fun x => x i₀ ∈ T) (Fintype.piFinset (fun _ : Fin n => S)) =
      Fintype.piFinset (Function.update (fun _ : Fin n => S) i₀ T) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Function.update_apply]
    constructor
    · rintro ⟨h1, h2⟩ i
      split_ifs with h
      · subst h; exact h2
      · exact h1 i
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · specialize h i
        split_ifs at h with hi
        · subst hi; exact hT h
        · exact h
      · specialize h i₀
        simpa using h
  rw [h_set, Fintype.card_piFinset]
  have h1 : (fun i : Fin n => (Function.update (fun _ : Fin n => S) i₀ T i).card) =
      Function.update (fun _ : Fin n => S.card) i₀ T.card := by
    ext i
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  rw [h1]
  have hmem : i₀ ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i₀
  rw [Finset.prod_update_of_mem hmem]
  have h_sdiff : ((Finset.univ : Finset (Fin n)) \ {i₀}) = Finset.univ.erase i₀ :=
    Finset.sdiff_singleton_eq_erase i₀ Finset.univ
  rw [h_sdiff, Finset.prod_const, Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
