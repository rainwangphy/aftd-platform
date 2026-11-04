import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.JensenShannonGenerator
import AFTD.Kb.Tcs.MutualFInformation

/-!
# jensen_shannon_binary_cid_not_subadditive

Topic: information   Node: 063f994922ab

Provenance: helper lemma. arXiv:2610.21231

There exists a binary Markov chain with conditionally identically distributed observations Y, Z given X where the unregularized Jensen-Shannon mutual information strictly violates subadditivity.
-/

/-- The unregularized Jensen-Shannon mutual information is not subadditive on binary Markov chains with conditionally identically distributed observations. -/
theorem jensen_shannon_binary_cid_not_subadditive :
    ∃ (pX : Fin 2 → ℝ) (P : Fin 2 → Fin 2 → ℝ),
      (∀ x, 0 ≤ pX x) ∧ (∑ x, pX x = 1) ∧
      (∀ x y, 0 ≤ P x y) ∧ (∀ x, ∑ y, P x y = 1) ∧
      2 * mutual_f_information jensen_shannon_generator (fun x y => pX x * P x y) <
        mutual_f_information jensen_shannon_generator
          (fun x (yz : Fin 2 × Fin 2) => pX x * P x yz.1 * P x yz.2) := by
  refine ⟨fun x => if x = 0 then (99:ℝ)/100 else 1/100,
          fun x y => if x = 0 then (if y = 0 then (99:ℝ)/100 else 1/100) else (if y = 0 then 7/10 else 3/10),
          ?_, ?_, ?_, ?_, ?_⟩
  · intro x; fin_cases x <;> norm_num
  · simp only [Fin.sum_univ_two]; norm_num
  · intro x y; fin_cases x <;> fin_cases y <;> norm_num
  · intro x; fin_cases x <;> simp only [Fin.sum_univ_two] <;> norm_num
  · simp only [mutual_f_information, jensen_shannon_generator, Fin.sum_univ_two, Fintype.sum_prod_type]
    simp only [Fin.isValue, if_true, if_false, Fin.reduceEq]
    norm_num
    num_ineq
