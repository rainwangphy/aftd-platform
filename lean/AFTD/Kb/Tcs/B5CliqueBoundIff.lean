import AFTD.Prelude
import AFTD.Kb.Tcs.B5Graph
import AFTD.Kb.Tcs.B5QuotientMatrix
import AFTD.Kb.Tcs.B5QuotientTraceSq
import AFTD.Kb.Tcs.B5CliqueNum
import AFTD.Kb.Tcs.B5GapNonneg
import AFTD.Kb.Tcs.B5CliqueBoundFailsOfExceptional

/-!
# b5_clique_bound_iff

Topic: graphs   Node: bc4b990495b1

Provenance: original. Related work: arXiv:2610.21388 (Stronger spectral bound for clique number): Theorems 3.1 and 3.5 prove the bound for B_3 and B_4 with one exceptional family / one exceptional graph; the example after Theorem 3.5 shows it fails for B_5(1,2,1,1,1) and says that for t = 5 'there may be additional parameter choices for which our bound fails'. This characterizes them

For B_5(n_0..n_4) with all n_i ≥ 1, the strong spectral clique bound sqrt(Σ_{λ ≠ -1} λ^2) ≤ n(1 - 1/ω) (with Σ_{λ≠-1} λ^2 = tr(M^2) for the quotient matrix M) holds if and only if (n_0, n_1, n_2, n_3) is not (1,1,1,1), (1,1,1,2) or (1,2,1,1) (in the paper's vertex order r_1, r_2, w_1, w_2, r_3); so it fails exactly on three infinite one-parameter families B_5(1,1,1,1,c), B_5(1,1,1,2,c), B_5(1,2,1,1,c).
-/

theorem b5_clique_bound_iff (n : Fin 5 → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    Real.sqrt ((b5_quotient_matrix n ^ 2).trace)
        ≤ (∑ i, (n i : ℝ)) * (1 - 1 / ((b5_graph n).cliqueNum : ℝ)) ↔
      ¬ (n 0 = 1 ∧ n 2 = 1 ∧ ((n 1 = 1 ∧ n 3 = 1) ∨ (n 1 = 1 ∧ n 3 = 2) ∨ (n 1 = 2 ∧ n 3 = 1))) := by
  rw [b5_quotient_trace_sq, b5_cliqueNum]
  simp only [Fin.sum_univ_five]
  have hW1 : (1:ℝ) ≤ ((n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) : ℕ) : ℝ) := by
    have h := hpos 4
    have h2 : (1:ℕ) ≤ n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) :=
      le_trans h (Nat.le_add_right _ _)
    exact_mod_cast h2
  have hWpos : (0:ℝ) < ((n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) : ℕ) : ℝ) :=
    lt_of_lt_of_le zero_lt_one hW1
  have hfrac : (0:ℝ) ≤ 1 - 1 / ((n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) : ℕ) : ℝ) := by
    have h3 : (1:ℝ) / ((n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hWpos]; exact hW1
    linarith
  have hNnn : (0:ℝ) ≤ (↑(n 0) + ↑(n 1) + ↑(n 2) + ↑(n 3) + ↑(n 4)) := by positivity
  have hY : (0:ℝ) ≤ (↑(n 0) + ↑(n 1) + ↑(n 2) + ↑(n 3) + ↑(n 4)) * (1 - 1 / ((n 4 + max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) : ℕ) : ℝ)) :=
    mul_nonneg hNnn hfrac
  rw [Real.sqrt_le_left hY]
  have hsq : ∀ A B : ℝ, (A * B) ^ 2 = A ^ 2 * B ^ 2 := fun A B => by ring
  constructor
  · intro hle hexc
    have hgt := b5_clique_bound_fails_of_exceptional (n 0) (n 1) (n 2) (n 3) (n 4) (hpos 4) hexc
    rw [hsq] at hle
    linarith
  · intro hne
    have hge := b5_gap_nonneg (n 0) (n 1) (n 2) (n 3) (n 4) (hpos 0) (hpos 1) (hpos 2) (hpos 3) (hpos 4) hne
    rwa [hsq]
