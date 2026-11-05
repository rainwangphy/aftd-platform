import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetTransversalNumber

/-!
# finset_transversal_number_mono

Topic: graphs   Node: 32f8dca01aeb

Provenance: helper lemma. step towards op_979_csym_max_nullity_lt_fort_transversal_number

For any two finite collections C1 ⊆ C2 of nonempty subsets of a finite set V, the transversal number of C1 is at most the transversal number of C2.
-/

/-- The transversal number of a subcollection is at most the transversal number of the larger collection, provided every set in the larger collection is nonempty. -/
theorem finset_transversal_number_mono {V : Type*} [Fintype V] [DecidableEq V]
    {C1 C2 : Finset (Finset V)} (h : C1 ⊆ C2) (hne : ∀ S ∈ C2, S.Nonempty) :
    finset_transversal_number C1 ≤ finset_transversal_number C2 := by
  unfold finset_transversal_number
  set S1 := { k : ℕ | ∃ T : Finset V, (∀ S ∈ C1, (T ∩ S).Nonempty) ∧ T.card = k }
  set S2 := { k : ℕ | ∃ T : Finset V, (∀ S ∈ C2, (T ∩ S).Nonempty) ∧ T.card = k }
  have hS2_nonempty : S2.Nonempty := by
    refine ⟨(Finset.univ : Finset V).card, Finset.univ, ?_, rfl⟩
    intro S hS
    rw [Finset.univ_inter]
    exact hne S hS
  have hmem : sInf S2 ∈ S2 := Nat.sInf_mem hS2_nonempty
  rcases hmem with ⟨T, hT, hTcard⟩
  have hmem1 : sInf S2 ∈ S1 := by
    refine ⟨T, ?_, hTcard⟩
    intro S hS
    exact hT S (h hS)
  exact Nat.sInf_le hmem1
