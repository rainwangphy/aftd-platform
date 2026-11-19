import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.NotMatroidConnectedOfNotIndepSingleton
import AFTD.Kb.Tcs.NotMatroidConnectedOfIndepGround

/-!
# matroid_connected_fin_two_iff

Topic: algorithms   Node: c1324f27af1f

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A matroid on the two-element ground set Fin 2 is connected if and only if {0} and {1} are independent and {0, 1} is dependent (it is the uniform matroid of rank 1).
-/

theorem matroid_connected_fin_two_iff (M : Matroid (Fin 2)) (hE : M.E = Set.univ) :
    matroid_connected M ↔ M.Indep {0} ∧ M.Indep {1} ∧ ¬ M.Indep Set.univ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · by_contra hd
      exact not_matroid_connected_of_not_indep_singleton M 0 1 (by simp [hE]) (by simp [hE]) (by decide) hd h
    · by_contra hd
      exact not_matroid_connected_of_not_indep_singleton M 1 0 (by simp [hE]) (by simp [hE]) (by decide) hd h
    · intro hd
      exact not_matroid_connected_of_indep_ground M 0 1 (by simp [hE]) (by simp [hE]) (by decide) (hE ▸ hd) h
  · rintro ⟨h0, h1, h2⟩
    have hC : M.IsCircuit Set.univ := by
      rw [Matroid.isCircuit_iff_forall_ssubset]
      refine ⟨⟨h2, by simp [hE]⟩, fun I hI => ?_⟩
      obtain ⟨x, -, hx⟩ := Set.exists_of_ssubset hI
      have : I ⊆ {0} ∨ I ⊆ {1} := by
        fin_cases x
        · right; intro y hy
          fin_cases y
          · exact absurd hy hx
          · rfl
        · left; intro y hy
          fin_cases y
          · rfl
          · exact absurd hy hx
      rcases this with h | h
      · exact h0.subset h
      · exact h1.subset h
    intro e _ f _
    exact Or.inr ⟨Set.univ, hC, trivial, trivial⟩
