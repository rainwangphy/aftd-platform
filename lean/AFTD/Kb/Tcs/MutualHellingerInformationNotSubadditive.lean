import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.PowerDivergenceHalfRootBounds

/-!
# mutual_hellinger_information_not_subadditive

Topic: information   Node: c2bbaa1b6710

Provenance: original. Related work: arXiv:2610.21231 (On the subadditivity of mutual f-information), question after Theorem 1: "in particular, does subadditivity hold for the Hellinger case β = 1/2?" Answered in the negative.

Subadditivity fails in the Hellinger case β = 1/2: there are binary random variables X, Y, Z with Y ← X → Z and Ĩ_{f_{1/2}}(X; YZ) > Ĩ_{f_{1/2}}(X; Y) + Ĩ_{f_{1/2}}(X; Z). Instance: P(X = 0) = 1/300; P(Y = 0 | X = 0) = 1/3, P(Y = 0 | X = 1) = 1/300; Z is Y's channel mirrored, P(Z = z | x) = P(Y = 1 − z | x).
-/

theorem mutual_hellinger_information_not_subadditive :
    ∃ (pX : Fin 2 → ℝ) (PY PZ : Fin 2 → Fin 2 → ℝ),
      (∀ x, 0 ≤ pX x) ∧ ∑ x, pX x = 1 ∧ (∀ x y, 0 ≤ PY x y) ∧ (∀ x, ∑ y, PY x y = 1) ∧
      (∀ x z, 0 ≤ PZ x z) ∧ (∀ x, ∑ z, PZ x z = 1) ∧
      mutual_f_information (power_divergence_generator (1 / 2)) (fun x y => pX x * PY x y) +
          mutual_f_information (power_divergence_generator (1 / 2)) (fun x z => pX x * PZ x z) <
        mutual_f_information (power_divergence_generator (1 / 2))
          (fun x (yz : Fin 2 × Fin 2) => pX x * PY x yz.1 * PZ x yz.2) := by
  refine ⟨![1/300, 299/300], ![![1/3, 2/3], ![1/300, 299/300]],
    ![![2/3, 1/3], ![299/300, 1/300]], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; fin_cases x <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · intro x y; fin_cases x <;> fin_cases y <;> norm_num
  · intro x; fin_cases x <;> simp [Fin.sum_univ_two] <;> norm_num
  · intro x y; fin_cases x <;> fin_cases y <;> norm_num
  · intro x; fin_cases x <;> simp [Fin.sum_univ_two] <;> norm_num
  · obtain ⟨l0, u0⟩ := power_divergence_half_root_bounds (100 / 3433) (170672322461 / 1000000000000) (85336161231 / 500000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l1, u1⟩ := power_divergence_half_root_bounds (4000000 / 8923633) (669513202051 / 1000000000000) (167378300513 / 250000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l2, u2⟩ := power_divergence_half_root_bounds (20000 / 29867) (818312521921 / 1000000000000) (409156260961 / 500000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l3, u3⟩ := power_divergence_half_root_bounds (100 / 133) (216777492381 / 250000000000) (34684398781 / 40000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l4, u4⟩ := power_divergence_half_root_bounds (29900 / 36467) (90549399731 / 100000000000) (905493997311 / 1000000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l5, u5⟩ := power_divergence_half_root_bounds (29900 / 29867) (40022091867 / 40000000000) (250138074169 / 250000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l6, u6⟩ := power_divergence_half_root_bounds (8940100 / 8923633) (1000922237067 / 1000000000000) (250230559267 / 250000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l7, u7⟩ := power_divergence_half_root_bounds (2000000 / 36467) (7405680632443 / 1000000000000) (1851420158111 / 250000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l8, u8⟩ := power_divergence_half_root_bounds (10000 / 133) (8671099695241 / 1000000000000) (4335549847621 / 500000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨l9, u9⟩ := power_divergence_half_root_bounds (1000000 / 3433) (17067232246187 / 1000000000000) (4266808061547 / 250000000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [mutual_f_information, power_divergence_generator, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num at l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 l8 u8 l9 u9 ⊢
    linarith
