import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.MatroidConnectedFinTwoIff
import AFTD.Kb.Tcs.ExistsMatroidOfIndepTable
import AFTD.Kb.Tcs.MatroidConnectednessQueryNotLeOfSensitive
import AFTD.Kb.Tcs.NotMatroidConnectedOfNotIndepSingleton
import AFTD.Kb.Tcs.NotMatroidConnectedOfIndepGround
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval

/-!
# matroid_connectedness_query_two_eq_three

Topic: algorithms   Node: c319e83dec35

Provenance: original. Related work: Smallest case of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Final remarks: is the independence-query complexity of matroid connectedness linear?). The paper proves the lower bound n (Proposition 2); the exact value D(2) = 3 = 2n - 1 was found by exhaustive search (experiments 33679, 33956).

Here matroid_connectedness_query_le n q means: some deterministic independence-query decision tree of depth at most q decides, for every matroid with ground set Fin n, whether it is connected (any two distinct elements lie in a common circuit). On a two-element ground set the deterministic independence-query complexity of deciding matroid connectedness is exactly 3: matroid_connectedness_query_le 2 3 holds and matroid_connectedness_query_le 2 2 does not.
-/

theorem matroid_connectedness_query_two_eq_three :
    matroid_connectedness_query_le 2 3 ∧ ¬ matroid_connectedness_query_le 2 2 := by
  refine ⟨?_, ?_⟩
  · refine ⟨.query {0} (.leaf false) (.query {1} (.leaf false) (.query Finset.univ (.leaf true) (.leaf false))),
      by decide, fun M hE o ho => ?_⟩
    rw [matroid_connected_fin_two_iff M hE]
    have h0 := ho {0}
    have h1 := ho {1}
    have h2 := ho Finset.univ
    simp only [Finset.coe_singleton, Finset.coe_univ] at h0 h1 h2
    rw [← h0, ← h1, ← h2]
    simp only [MatroidIndepQueryTree.eval]
    cases o {0} <;> cases o {1} <;> cases o Finset.univ <;> simp
  · obtain ⟨M, hME, hM⟩ := exists_matroid_of_indep_table (n := 2) (fun S => decide (S.card ≤ 1))
      (by decide) (by decide) (by decide)
    have key : ∀ A : Finset (Fin 2), ∃ N : Matroid (Fin 2), N.E = Set.univ ∧
        ∀ S : Finset (Fin 2), N.Indep (S : Set (Fin 2)) ↔ S ⊆ A := by
      intro A
      obtain ⟨N, hNE, hN⟩ := exists_matroid_of_indep_table (n := 2) (fun S => decide (S ⊆ A))
        (by simp) (fun I J hJ hIJ => by simp only [decide_eq_true_eq] at hJ ⊢; exact hIJ.trans hJ)
        (fun I J hI hJ hIJ => by
          simp only [decide_eq_true_eq] at hI hJ ⊢
          obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hIJ
          exact ⟨e, heJ, heI, Finset.insert_subset (hJ heJ) hI⟩)
      exact ⟨N, hNE, fun S => by simpa using hN S⟩
    refine matroid_connectedness_query_not_le_of_sensitive M hME ?_
      ({{0}, {1}, Finset.univ} : Finset (Finset (Fin 2))) ?_ 2 (by decide)
    · rw [matroid_connected_fin_two_iff M hME]
      have h0 := hM {0}
      have h1 := hM {1}
      have h2 := hM Finset.univ
      simp only [Finset.coe_singleton, Finset.coe_univ] at h0 h1 h2
      rw [h0, h1, h2]; decide
    · intro S hS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hS
      rcases hS with rfl | rfl | rfl
      · obtain ⟨N, hNE, hN⟩ := key {1}
        refine ⟨N, hNE, ?_, ?_⟩
        · refine not_matroid_connected_of_not_indep_singleton N 0 1 (by simp [hNE]) (by simp [hNE]) (by decide) ?_
          have := hN {0}
          simp only [Finset.coe_singleton] at this
          rw [this]; decide
        · intro S' hS'
          rw [hN, hM]
          revert S'; decide
      · obtain ⟨N, hNE, hN⟩ := key {0}
        refine ⟨N, hNE, ?_, ?_⟩
        · refine not_matroid_connected_of_not_indep_singleton N 1 0 (by simp [hNE]) (by simp [hNE]) (by decide) ?_
          have := hN {1}
          simp only [Finset.coe_singleton] at this
          rw [this]; decide
        · intro S' hS'
          rw [hN, hM]
          revert S'; decide
      · obtain ⟨N, hNE, hN⟩ := key Finset.univ
        refine ⟨N, hNE, ?_, ?_⟩
        · refine not_matroid_connected_of_indep_ground N 0 1 (by simp [hNE]) (by simp [hNE]) (by decide) ?_
          have := hN Finset.univ
          simp only [Finset.coe_univ] at this
          rw [hNE, this]
        · intro S' hS'
          rw [hN, hM]
          revert S'; decide
