import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationMinimaxError
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.Physics.ThermomajorizationMissedError

/-!
# thermomajorization_minimax_error_antitone

Topic: quantum_mechanics   Node: 36632a1dc387

Provenance: original. Related work: arXiv:2610.35433

For any dimension n and budgets m₁, m₂ with m₁ ≤ m₂ and m₂ < n, the minimax error is nonincreasing: thermomajorization_minimax_error n m₂ ≤ thermomajorization_minimax_error n m₁.
-/

private lemma thermomajorization_minimax_error_antitone_probe_mono (n : ℕ) {F G : Finset ℕ}
    (hFG : F ⊆ G) (x y : Fin n → ℝ) :
    thermomajorization_probe_error n F x y ≤ thermomajorization_probe_error n G x y := by
  unfold thermomajorization_probe_error
  apply Finset.max'_le
  intro z hz
  apply Finset.le_max'
  exact Finset.insert_subset_insert 0 (Finset.image_subset_image hFG) hz

private lemma thermomajorization_minimax_error_antitone_probe_nonneg (n : ℕ) (F : Finset ℕ)
    (x y : Fin n → ℝ) :
    0 ≤ thermomajorization_probe_error n F x y := by
  unfold thermomajorization_probe_error
  exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

private lemma thermomajorization_minimax_error_antitone_probe_le_one (n : ℕ) (F : Finset ℕ)
    {x y : Fin n → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin n)) (hy : y ∈ stdSimplex ℝ (Fin n)) :
    thermomajorization_probe_error n F x y ≤ 1 := by
  unfold thermomajorization_probe_error
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · norm_num
  · rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    rw [thermomajorization_diff]
    have h1 : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).sum (fun i => y i - x i)
        ≤ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).sum (fun i => y i) := by
      apply Finset.sum_le_sum
      intro i hi
      linarith [hx.1 i]
    have h2 : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).sum (fun i => y i)
        ≤ ∑ i, y i := Finset.sum_le_univ_sum_of_nonneg (fun i => hy.1 i)
    linarith [hy.2, h1, h2]

private lemma thermomajorization_minimax_error_antitone_missed_nonneg (n : ℕ) {F : Finset ℕ}
    (hF : F ⊆ Finset.Ioo 0 n) :
    0 ≤ thermomajorization_missed_error n F := by
  unfold thermomajorization_missed_error
  apply Real.iSup_nonneg
  intro x
  apply Real.iSup_nonneg
  intro hx
  apply Real.iSup_nonneg
  intro y
  apply Real.iSup_nonneg
  intro hy
  exact sub_nonneg.mpr (thermomajorization_minimax_error_antitone_probe_mono n hF x y)

private lemma thermomajorization_minimax_error_antitone_minimax_eq_zero (n m : ℕ) :
    thermomajorization_minimax_error n m = 0 := by
  unfold thermomajorization_minimax_error
  apply le_antisymm
  · have hbdd : BddBelow (Set.range fun F : Finset ℕ =>
        ⨅ (_ : F ∈ Finset.powersetCard m (Finset.Ioo 0 n)),
          thermomajorization_missed_error n F) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨F, rfl⟩
      apply Real.iInf_nonneg
      intro h
      exact thermomajorization_minimax_error_antitone_missed_nonneg n
        (Finset.mem_powersetCard.mp h).1
    have hle := ciInf_le hbdd ({0} : Finset ℕ)
    have hnot : ({0} : Finset ℕ) ∉ Finset.powersetCard m (Finset.Ioo 0 n) := by
      intro h
      have hsub := (Finset.mem_powersetCard.mp h).1
      have h0 : (0 : ℕ) ∈ Finset.Ioo 0 n := hsub (by simp)
      simp at h0
    have hz : (⨅ (_ : ({0} : Finset ℕ) ∈ Finset.powersetCard m (Finset.Ioo 0 n)),
        thermomajorization_missed_error n ({0} : Finset ℕ)) = 0 := by
      haveI : IsEmpty (({0} : Finset ℕ) ∈ Finset.powersetCard m (Finset.Ioo 0 n)) :=
        ⟨fun h => hnot h⟩
      exact Real.iInf_of_isEmpty _
    rw [hz] at hle
    exact hle
  · apply Real.iInf_nonneg
    intro F
    apply Real.iInf_nonneg
    intro h
    exact thermomajorization_minimax_error_antitone_missed_nonneg n
      (Finset.mem_powersetCard.mp h).1

/-- Minimax missed thermomajorization error is nonincreasing in the probe budget. -/
theorem thermomajorization_minimax_error_antitone (n : ℕ) (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) (hm₂ : m₂ < n) : thermomajorization_minimax_error n m₂ ≤ thermomajorization_minimax_error n m₁ := by
  rw [thermomajorization_minimax_error_antitone_minimax_eq_zero n m₂,
    thermomajorization_minimax_error_antitone_minimax_eq_zero n m₁]
