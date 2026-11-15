import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationMinimaxError
import AFTD.Kb.Physics.ThermomajorizationMissedError

/-!
# not_thermomajorization_zero_budget_error

Topic: quantum_mechanics   Node: 4bcc65d33049

Provenance: original. Related work: refutes `thermomajorization_zero_budget_error`

The statement `thermomajorization_zero_budget_error` is false: The formal definition `thermomajorization_minimax_error n m := ⨅ F ∈ Finset.powersetCard m (Finset.Ioo 0 n), thermomajorization_missed_error n F` uses Lean's `⨅ F ∈ s, _` notation, which elaborates to the nested `iInf` `⨅ F : Finset ℕ, ⨅ (_ : F ∈ s), _`, ranging over ALL finsets — not the finset-wise infimum over the members of `powersetCard`. For `m = 0`, a nonzero-cardinality finset such as `F = {0}` is not a member of `powersetCard 0 (Ioo 0 2)`, so the inner `iInf` is over an empty index type and equals `sInf ∅ = 0` (`iInf_of_isEmpty`, `Real.sInf_empty`). The range is bounded below (all values lie in `{0} ∪ {missed_error n ∅}`), so `ciInf_le` gives `thermomajorization_minimax_error n 0 ≤ 0`. But for `n = 2`, `1 - (2:ℝ)⁻¹ = 1/2 > 0`, so the claimed equality fails. This is a formalization artifact: the *intended* infimum over the actual subsets is indeed `1 - 1/n`, but the literal Lean term is `0` (more precisely `min 0 (missed_error n ∅)`).
-/

theorem not_thermomajorization_zero_budget_error : ¬ (∀ (n : ℕ) (hn : 2 ≤ n), thermomajorization_minimax_error n 0 = 1 - (n : ℝ)⁻¹) := by
  intro H
  have hle : thermomajorization_minimax_error 2 0 ≤ 0 := by
    unfold thermomajorization_minimax_error
    have hbdd : BddBelow (Set.range (fun F : Finset ℕ =>
        ⨅ (_ : F ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)),
          thermomajorization_missed_error 2 F)) := by
      refine ⟨min 0 (thermomajorization_missed_error 2 ∅), ?_⟩
      rintro _ ⟨F, rfl⟩
      dsimp only
      by_cases hF : F ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)
      · have hFe : F = ∅ := by
          rw [Finset.powersetCard_zero] at hF
          simpa using hF
        subst hFe
        haveI : Nonempty (∅ ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)) := ⟨hF⟩
        rw [ciInf_const]
        exact min_le_right _ _
      · haveI : IsEmpty (F ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)) := ⟨fun h => hF h⟩
        rw [iInf_of_isEmpty]
        simp only [Real.sInf_empty]
        exact min_le_left _ _
    have h0 : (⨅ (_ : ({0} : Finset ℕ) ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)),
        thermomajorization_missed_error 2 {0}) = 0 := by
      haveI : IsEmpty (({0} : Finset ℕ) ∈ Finset.powersetCard 0 (Finset.Ioo 0 2)) := by
        constructor
        intro h
        rw [Finset.mem_powersetCard] at h
        simp at h
      rw [iInf_of_isEmpty]
      simp [Real.sInf_empty]
    have hci := ciInf_le hbdd ({0} : Finset ℕ)
    rw [h0] at hci
    exact hci
  have hH := H 2 (by norm_num)
  rw [hH] at hle
  norm_num at hle
