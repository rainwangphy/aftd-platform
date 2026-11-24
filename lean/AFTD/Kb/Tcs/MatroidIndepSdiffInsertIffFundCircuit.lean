import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# matroid_indep_sdiff_insert_iff_fund_circuit

Topic: algorithms   Node: 8cf58bcc9201

Provenance: helper lemma. step towards matroid_connectedness_query_linear

For any matroid M, base B, element e ∉ B in the ground set, and subset A ⊆ B, the set insert e (B \ A) is independent if and only if the fundamental circuit M.fundCircuit e B meets A. This enables testing fundamental-graph cut connectivity in 1 query.
-/

/-- For a base B, element e not in B, and subset A ⊆ B, insert e (B \ A) is independent iff the fundamental circuit of e meets A. -/
theorem matroid_indep_sdiff_insert_iff_fund_circuit {α : Type*} (M : Matroid α) {B : Set α} (hB : M.IsBase B) {e : α} (heE : e ∈ M.E) (heB : e ∉ B) {A : Set α} (hA : A ⊆ B) : M.Indep (insert e (B \ A)) ↔ (M.fundCircuit e B ∩ A).Nonempty := by
  have heA : e ∉ A := fun h => heB (hA h)
  constructor
  · intro hindep
    by_contra hdisj
    have h_empty : M.fundCircuit e B ∩ A = ∅ := Set.not_nonempty_iff_eq_empty.mp hdisj
    have hd : Disjoint (M.fundCircuit e B) A := Set.disjoint_iff_inter_eq_empty.mpr h_empty
    have hsub : M.fundCircuit e B ⊆ insert e B \ A :=
      Disjoint.le_sdiff_of_le_left hd (M.fundCircuit_subset_insert e B)
    rw [Set.insert_sdiff_of_notMem B heA] at hsub
    have hcirc_indep : M.Indep (M.fundCircuit e B) := hindep.subset hsub
    exact (hB.fundCircuit_isCircuit heE heB).not_indep hcirc_indep
  · intro hmeet
    by_contra hnot
    have hsub_ground : insert e (B \ A) ⊆ M.E :=
      Set.insert_subset heE (Set.sdiff_subset.trans hB.subset_ground)
    have hdep : M.Dep (insert e (B \ A)) := M.dep_of_not_indep hnot hsub_ground
    obtain ⟨C, hCsub, hC⟩ := hdep.exists_isCircuit_subset
    have hCB : C ⊆ insert e B := hCsub.trans (Set.insert_subset_insert Set.sdiff_subset)
    have hC_eq : C = M.fundCircuit e B := hC.eq_fundCircuit_of_subset hB.indep hCB
    have hdisj_insert : Disjoint (insert e (B \ A)) A := by
      rw [Set.disjoint_insert_left]
      exact ⟨heA, Set.disjoint_sdiff_left⟩
    have hdisj_C : Disjoint C A := hdisj_insert.mono_left hCsub
    rw [hC_eq] at hdisj_C
    obtain ⟨x, hxC, hxA⟩ := hmeet
    exact (Set.disjoint_left.1 hdisj_C) hxC hxA
