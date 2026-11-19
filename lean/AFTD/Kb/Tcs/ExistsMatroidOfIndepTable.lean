import AFTD.Prelude

/-!
# exists_matroid_of_indep_table

Topic: algorithms   Node: 2961ebe128b8

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A Boolean table o on the subsets of Fin n that is true on the empty set, closed under taking subsets and satisfies the augmentation axiom is the independence oracle of a matroid with ground set Fin n.
-/

theorem exists_matroid_of_indep_table {n : ℕ} (o : Finset (Fin n) → Bool) (h0 : o ∅ = true)
    (hsub : ∀ I J : Finset (Fin n), o J = true → I ⊆ J → o I = true)
    (haug : ∀ I J : Finset (Fin n), o I = true → o J = true → I.card < J.card →
      ∃ e ∈ J, e ∉ I ∧ o (insert e I) = true) :
    ∃ M : Matroid (Fin n), M.E = Set.univ ∧ ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ o S = true := by
  exact ⟨(IndepMatroid.ofFinset (Set.univ : Set (Fin n)) (fun S => o S = true) h0
      (fun I J hJ hIJ => hsub I J hJ hIJ) (fun I J hI hJ hIJ => haug I J hI hJ hIJ)
      (fun _ _ => Set.subset_univ _)).matroid, rfl, fun S => by simp⟩
