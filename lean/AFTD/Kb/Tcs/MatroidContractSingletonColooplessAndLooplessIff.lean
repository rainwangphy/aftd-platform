import AFTD.Prelude

/-!
# matroid_contract_singleton_coloopless_and_loopless_iff

Topic: combinatorics   Node: 1a88b5a4f3f4

Provenance: formalization of a published result. Source: arXiv:2610.27706 Lemma 2.1(ii)

Let M be a finite loopless and coloopless matroid on α and e ∈ M.E. Then the single-element contraction M.contract {e} is coloopless (i.e. (M.contract {e})✶.Loopless), and (M.contract {e}) is loopless if and only if e belongs to no two-element circuit of M (¬ ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C.ncard = 2).
-/

/-- Contracting an element from a loopless and coloopless matroid produces a coloopless matroid, which is loopless if and only if the element belongs to no 2-element circuit. -/
theorem matroid_contract_singleton_coloopless_and_loopless_iff
    {α : Type*} (M : Matroid α) [M.Finite] [M.Loopless] [M✶.Loopless]
    (e : α) (he : e ∈ M.E) :
    (M.contract {e})✶.Loopless ∧
    ((M.contract {e}).Loopless ↔ ¬ ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C.ncard = 2) := by
  refine ⟨?_, ?_⟩
  · rw [Matroid.dual_contract, Matroid.loopless_iff, Matroid.delete_loops_eq, Matroid.loops_eq_empty, Set.empty_sdiff]
  · rw [Matroid.loopless_iff, Matroid.contract_loops_eq, Set.eq_empty_iff_forall_notMem]
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not]
    constructor
    · intro h ⟨C, hC, heC, hcard⟩
      obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 hcard
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heC
      rcases heC with rfl | rfl
      · have hyC : y ∈ ({e, y} : Set α) := by simp
        have hcl := hC.mem_closure_sdiff_singleton_of_mem hyC
        have : ({e, y} : Set α) \ {y} = {e} := by simp [hxy]
        rw [this] at hcl
        exact hxy.symm (h y hcl)
      · have hxC : x ∈ ({x, e} : Set α) := by simp
        have hcl := hC.mem_closure_sdiff_singleton_of_mem hxC
        have : ({x, e} : Set α) \ {x} = {e} := by simp [Ne.symm hxy]
        rw [this] at hcl
        exact hxy (h x hcl)
    · intro h f hf
      by_contra hfe
      apply h
      have hf_not : f ∉ ({e} : Set α) := by simpa
      obtain ⟨C, hCsub, hC, hfC⟩ := (Matroid.mem_closure_iff_exists_isCircuit hf_not).1 hf
      have heC : e ∈ C := by
        by_contra heC
        have : C = {f} := by
          ext x
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hxC
            have := hCsub hxC
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
            obtain rfl | rfl := this
            · rfl
            · exact (heC hxC).elim
          · rintro rfl
            exact hfC
        subst this
        have hloop := Matroid.singleton_isCircuit.1 hC
        exact M.not_isLoop f hloop
      have hCeq : C = {f, e} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        refine ⟨fun hx ↦ hCsub hx, fun hx ↦ ?_⟩
        obtain rfl | rfl := hx
        · exact hfC
        · exact heC
      refine ⟨C, hC, heC, ?_⟩
      rw [hCeq, Set.ncard_pair hfe]
