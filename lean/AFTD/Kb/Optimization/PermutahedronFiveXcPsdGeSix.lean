import AFTD.Prelude
import AFTD.Kb.Optimization.PermutahedronSlackMatrix
import AFTD.Kb.Optimization.MatrixHasPsdFactorizationOfNonneg
import AFTD.Kb.Optimization.MatrixHasPsdFactorizationRestrictZeroRow
import AFTD.Kb.Optimization.HexagonSlackNotPsdFactorizationLeThree
import AFTD.Kb.Optimization.MatrixHasPsdFactorizationSubmatrix
import AFTD.Kb.Optimization.MatrixPsdRank
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# permutahedron_five_xc_psd_ge_six

Topic: integer_programming   Node: 467e09b97165

Provenance: formalization of a published result. Source: arXiv:2610.04498 Sec. 4.2

The positive semidefinite rank of the slack matrix of the standard five-element permutahedron is at least 6.
-/

theorem finset_nat_choose_card_le_sum_succ (T : Finset ℕ) :
    Nat.choose (T.card + 1) 2 ≤ ∑ v ∈ T, (v + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card this
    rw [Finset.sum_insert hna, Finset.card_insert_of_notMem hna]
    have hc : (s.card + 1 + 1).choose 2 = (s.card + 1) + (s.card + 1).choose 2 :=
      Nat.choose_succ_succ' (s.card + 1) 1 ▸ by rw [Nat.choose_one_right]
    omega

/-- The PSD rank of the 5-element permutahedron slack matrix is at least 6. -/
theorem permutahedron_five_xc_psd_ge_six : 6 ≤ matrix_psd_rank (permutahedron_slack_matrix 5) := by
  classical
  set M := permutahedron_slack_matrix 5 with hMdef
  have hent : ∀ (S : {S : Finset (Fin 5) // S.Nonempty ∧ S ≠ Finset.univ}) (σ : Equiv.Perm (Fin 5))
      (k : ℕ), (∑ x ∈ S.val, ((σ x).val + 1)) = Nat.choose (S.val.card + 1) 2 + k →
      M S σ = k := by
    intro S σ k hk
    have := congrArg (Nat.cast : ℕ → ℝ) hk
    push_cast at this
    simp only [hMdef, permutahedron_slack_matrix]
    linarith
  have hnonneg : ∀ S σ, 0 ≤ M S σ := by
    intro S σ
    have himg : (∑ x ∈ S.val, ((σ x).val + 1)) = ∑ v ∈ S.val.image (fun x => (σ x).val), (v + 1) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact σ.injective (Fin.ext hxy)
    have hc : (S.val.image (fun x => (σ x).val)).card = S.val.card := by
      rw [Finset.card_image_of_injective]
      intro x y hxy
      exact σ.injective (Fin.ext hxy)
    have hle := finset_nat_choose_card_le_sum_succ (S.val.image (fun x => (σ x).val))
    rw [hc, ← himg] at hle
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hent S σ k hk]
    positivity
  by_contra hlt
  push Not at hlt
  have hne : {r : ℕ | matrix_has_psd_factorization M r}.Nonempty :=
    ⟨_, matrix_has_psd_factorization_of_nonneg M hnonneg⟩
  have hmem : matrix_has_psd_factorization M (matrix_psd_rank M) := Nat.sInf_mem hne
  let F : Fin 6 → Finset (Fin 5) := ![{0}, {0, 2}, {2}, {1, 2}, {1}, {0, 1}]
  let V : Fin 6 → Equiv.Perm (Fin 5) := ![1, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 2, Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 1]
  have hF : ∀ i, (F i).Nonempty ∧ F i ≠ Finset.univ := by decide
  have hkey : ∀ i j : Fin 6, (∑ x ∈ F i, ((V j x).val + 1)) =
      Nat.choose ((F i).card + 1) 2 + (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (j - i) := by decide
  let S4 : {S : Finset (Fin 5) // S.Nonempty ∧ S ≠ Finset.univ} := ⟨{0, 1, 2, 3}, by decide⟩
  let S3 : {S : Finset (Fin 5) // S.Nonempty ∧ S ≠ Finset.univ} := ⟨{0, 1, 2}, by decide⟩
  have h4 : ∀ j, M S4 (V j) = 0 := by
    intro j
    have := hent S4 (V j) 0 (by revert j; decide)
    simpa using this
  have h3 : ∀ j, M S3 (V j) = 0 := by
    intro j
    have := hent S3 (V j) 0 (by revert j; decide)
    simpa using this
  have hz1 : M S4 (Equiv.swap 3 4) ≠ 0 := by
    rw [hent S4 _ 1 (by decide)]; norm_num
  have hz2 : M S3 (Equiv.swap 2 3) ≠ 0 := by
    rw [hent S3 _ 1 (by decide)]; norm_num
  have hs4 : M S4 (Equiv.swap 2 3) = 0 := by
    have := hent S4 (Equiv.swap 2 3) 0 (by decide)
    simpa using this
  have k1 := matrix_has_psd_factorization_restrict_zero_row M _ hmem S4 _ hz1
  have k2 := matrix_has_psd_factorization_restrict_zero_row _ _ k1 S3 ⟨_, hs4⟩ hz2
  have k3 := matrix_has_psd_factorization_submatrix _ _ (fun i => ⟨F i, hF i⟩)
    (fun j => ⟨⟨V j, h4 j⟩, h3 j⟩) k2
  apply hexagon_slack_not_psd_factorization_le_three (matrix_psd_rank M - 1 - 1) (by omega)
  convert k3 using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
  rw [hent ⟨F i, hF i⟩ (V j) _ (hkey i j)]
