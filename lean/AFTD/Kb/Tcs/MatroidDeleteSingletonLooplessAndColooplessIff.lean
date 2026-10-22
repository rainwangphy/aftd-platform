import AFTD.Prelude

/-!
# matroid_delete_singleton_loopless_and_coloopless_iff

Topic: combinatorics   Node: ccd0a258f84d

Provenance: formalization of a published result. Source: arXiv:2610.27706 Lemma 2.1(i)

Let M be a finite loopless and coloopless matroid on α and e ∈ M.E. Then the single-element deletion M.delete {e} is loopless; moreover, it is coloopless ((M.delete {e})✶.Loopless) if and only if e belongs to no two-element cocircuit of M (¬ ∃ C, M.IsCocircuit C ∧ e ∈ C ∧ C.ncard = 2).
-/

/-- Deleting an element from a loopless and coloopless matroid produces a loopless matroid; moreover, it is coloopless if and only if the element belongs to no 2-element cocircuit. -/
theorem matroid_delete_singleton_loopless_and_coloopless_iff
    {α : Type*} (M : Matroid α) [M.Finite] [M.Loopless] [M✶.Loopless]
    (e : α) (he : e ∈ M.E) :
    (M.delete {e}).Loopless ∧
    ((M.delete {e})✶.Loopless ↔ ¬ ∃ C, M.IsCocircuit C ∧ e ∈ C ∧ C.ncard = 2) := by
  refine ⟨(Matroid.delete_isRestriction M {e}).loopless, ?_⟩
  rw [Matroid.dual_delete, Matroid.loopless_iff, Matroid.contract_loops_eq, Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  have he_dual : e ∈ M✶.E := by rw [M.dual_ground]; exact he
  constructor
  · intro h ⟨C, hC, heC, hCcard⟩
    obtain ⟨f, hfe, rfl⟩ : ∃ f, f ≠ e ∧ C = {e, f} := by
      obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp hCcard
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
      rcases heC with rfl | rfl
      · exact ⟨y, hxy.symm, rfl⟩
      · exact ⟨x, hxy, by rw [Set.pair_comm]⟩
    have hmem : f ∈ ({e, f} : Set α) := Set.mem_insert_of_mem e rfl
    have hbas := hC.sdiff_singleton_isBasis hmem
    have hdiff : ({e, f} : Set α) \ {f} = {e} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hne⟩
        · rfl
        · contradiction
      · rintro rfl
        exact ⟨Or.inl rfl, hfe.symm⟩
    rw [hdiff] at hbas
    have hcl : f ∈ M✶.closure {e} := hbas.subset_closure (Set.mem_insert_of_mem e rfl)
    exact h f ⟨hcl, hfe⟩
  · intro h f ⟨hfcl, hfe⟩
    apply h
    have hI : M✶.Indep {e} := (Matroid.isNonloop_of_loopless he_dual).indep
    have heI : f ∉ ({e} : Set α) := by simp [hfe]
    have h_min : ∀ x ∈ ({e} : Set α), f ∉ M✶.closure ({e} \ {x}) := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      rw [Set.sdiff_self, Matroid.closure_empty, Matroid.loops_eq_empty]
      exact Set.notMem_empty f
    have hcirc := hI.insert_isCircuit_of_forall heI hfcl h_min
    rw [Set.pair_comm] at hcirc
    refine ⟨{e, f}, hcirc, Set.mem_insert _ _, ?_⟩
    rw [Set.ncard_eq_two]
    exact ⟨e, f, fun h => hfe h.symm, rfl⟩
