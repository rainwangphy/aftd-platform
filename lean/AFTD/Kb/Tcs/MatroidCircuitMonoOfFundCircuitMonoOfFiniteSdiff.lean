import AFTD.Prelude

/-!
# matroid_circuit_mono_of_fundCircuit_mono_of_finite_sdiff

Topic: algorithms   Node: 88a0810c0699

Provenance: helper lemma. step towards not_matroid_connected_of_fund_circuit_separated

Let B be a base of a matroid M and P a set of elements such that every fundamental circuit M.fundCircuit e B (e in E \ B) is monochromatic for the partition (P, E \ P): contained in P or disjoint from P. Then every circuit C with finitely many elements outside B is monochromatic for that partition.
-/

/-- Fundamental circuits that are each contained in P or disjoint from P force every circuit with a finite trace outside B to be so too. -/
theorem matroid_circuit_mono_of_fundCircuit_mono_of_finite_sdiff {α : Type*} (M : Matroid α) {B P : Set α} (hB : M.IsBase B) (hmono : ∀ e ∈ M.E \ B, M.fundCircuit e B ⊆ P ∨ Disjoint (M.fundCircuit e B) P) (C : Set α) (hC : M.IsCircuit C) (hfin : (C \ B).Finite) : C ⊆ P ∨ Disjoint C P := by
  have key : ∀ n, ∀ C, M.IsCircuit C → (C \ B).Finite → (C \ B).ncard ≤ n → C ⊆ P ∨ Disjoint C P := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih D hD hDfin hle
    have hne : (D \ B).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hDB : D ⊆ B := by
        intro x hx
        by_contra hxB
        have hmem : x ∈ D \ B := ⟨hx, hxB⟩
        rw [h] at hmem
        exact hmem
      exact hD.not_indep (hB.indep.subset hDB)
    obtain ⟨e, heD, heB⟩ := hne
    have heE : e ∈ M.E := hD.subset_ground heD
    have hFcirc : M.IsCircuit (M.fundCircuit e B) := hB.fundCircuit_isCircuit heE heB
    have heF : e ∈ M.fundCircuit e B := M.mem_fundCircuit e B
    have hFsdiff : M.fundCircuit e B \ {e} = M.fundCircuit e B ∩ B := M.fundCircuit_sdiff_eq_inter heB
    have hclaim : ∀ f ∈ D, (M.fundCircuit e B ⊆ P → f ∈ P) ∧ (Disjoint (M.fundCircuit e B) P → f ∉ P) := by
      intro f hfD
      by_cases hfF : f ∈ M.fundCircuit e B
      · exact ⟨fun h => h hfF, fun h => Set.disjoint_left.1 h hfF⟩
      · obtain ⟨C', hC'sub, hC'circ, hfC'⟩ := hD.strong_elimination hFcirc heD heF hfD hfF
        have heC' : e ∉ C' := by
          intro h
          exact (hC'sub h).2 (Set.mem_singleton_iff.mpr rfl)
        have hC'subB : C' \ B ⊆ (D \ B) \ {e} := by
          intro x hx
          obtain ⟨hxC', hxB⟩ := hx
          obtain ⟨hxU, hxe⟩ := hC'sub hxC'
          refine ⟨?_, hxe⟩
          rcases hxU with hxD | hxF
          · exact ⟨hxD, hxB⟩
          · exfalso
            have : x ∈ M.fundCircuit e B \ {e} := ⟨hxF, hxe⟩
            rw [hFsdiff] at this
            exact hxB this.2
        have hssub : C' \ B ⊆ D \ B := hC'subB.trans Set.sdiff_subset
        have hne2 : C' \ B ≠ D \ B := by
          intro heq
          have : e ∈ C' \ B := by
            rw [heq]; exact ⟨heD, heB⟩
          exact heC' this.1
        have hstrict : C' \ B ⊂ D \ B := Set.ssubset_iff_subset_ne.mpr ⟨hssub, hne2⟩
        have hfinlt : (C' \ B).ncard < (D \ B).ncard := Set.ncard_lt_ncard hstrict hDfin
        have hlt : (C' \ B).ncard < n := lt_of_lt_of_le hfinlt hle
        have hC'fin : (C' \ B).Finite := hDfin.subset hssub
        have hC'res := ih (C' \ B).ncard hlt C' hC'circ hC'fin le_rfl
        have hex : ∃ g ∈ C', g ∉ D := by
          by_contra h
          push Not at h
          have hCD : C' ⊆ D := fun g hg => h g hg
          have hEq : C' = D := hC'circ.eq_of_subset_isCircuit hD hCD
          rw [hEq] at hne2
          exact hne2 rfl
        obtain ⟨g, hgC', hgD⟩ := hex
        have hgF : g ∈ M.fundCircuit e B := by
          have h := hC'sub hgC'
          rcases h.1 with h' | h'
          · exact absurd h' hgD
          · exact h'
        refine ⟨fun hFP => ?_, fun hFP => ?_⟩
        · rcases hC'res with h | h
          · exact h hfC'
          · exact absurd (hFP hgF) (Set.disjoint_left.1 h hgC')
        · rcases hC'res with h | h
          · exact absurd (h hgC') (Set.disjoint_left.1 hFP hgF)
          · exact Set.disjoint_left.1 h hfC'
    rcases hmono e ⟨heE, heB⟩ with hFP | hFP
    · left
      exact fun f hf => (hclaim f hf).1 hFP
    · right
      exact Set.disjoint_left.2 fun f hf => (hclaim f hf).2 hFP
  exact key (C \ B).ncard C hC hfin le_rfl
