import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonAlgorithm
import AFTD.Kb.Tcs.ComparisonAlgorithmSuccessProb
import AFTD.Kb.Tcs.EmbeddingRangeContainsFraction
import AFTD.Kb.Tcs.LiftLinearOrderMinEq
import AFTD.Kb.Tcs.LinearOrderMin

/-!
# subset_transfer_two_comparisons

Topic: quantum   Node: 79933a1633ae

Provenance: formalization of a published result. Source: arXiv:2610.34762 Lemma 6

Suppose an algorithm on k objects succeeds in minimum selection with probability at least p on every strict order and uses at most two ordinary comparisons. For every n >= k, there exists an algorithm on n objects with the same comparison budget that succeeds with probability at least k * p / n on every strict order.
-/

/-- Subset transfer: an algorithm on `k` objects with success `p` transfers to `n ≥ k` with success `k*p/n`. -/
theorem subset_transfer_two_comparisons {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (A : ComparisonAlgorithm k 2) (p : ℝ)
    (hp : ∀ (L : LinearOrder (Fin k)), p ≤ comparison_algorithm_success_prob hk A L) :
    ∃ A' : ComparisonAlgorithm n 2, ∀ (hn : 0 < n) (L : LinearOrder (Fin n)),
      ((k : ℝ) * p) / (n : ℝ) ≤ comparison_algorithm_success_prob hn A' L := by
  classical
  have hNnat : 0 < Fintype.card (Fin k ↪ Fin n) := by
    have hne : Nonempty (Fin k ↪ Fin n) :=
      ⟨⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hkn⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩⟩
    exact Fintype.card_pos_iff.mpr hne
  have hNpos : (0 : ℝ) < (Fintype.card (Fin k ↪ Fin n) : ℝ) := by exact_mod_cast hNnat
  have hNne : (Fintype.card (Fin k ↪ Fin n) : ℝ) ≠ 0 := ne_of_gt hNpos
  refine ⟨⟨fun L i => (∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
      if f j = i then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) /
      (Fintype.card (Fin k ↪ Fin n) : ℝ), ?_, ?_⟩, ?_⟩
  · intro L i
    apply div_nonneg _ (le_of_lt hNpos)
    apply Finset.sum_nonneg
    intro f _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact A.nonneg _ _
    · exact le_refl 0
  · intro L
    have hsum : (∑ i : Fin n, ∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
            (if f j = i then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0))
        = (Fintype.card (Fin k ↪ Fin n) : ℝ) := by
      calc ∑ i : Fin n, ∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
            (if f j = i then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0)
        = ∑ f : Fin k ↪ Fin n, ∑ i : Fin n, ∑ j : Fin k,
            (if f j = i then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) := Finset.sum_comm
      _ = ∑ f : Fin k ↪ Fin n, ∑ j : Fin k, ∑ i : Fin n,
            (if f j = i then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) := by
            apply Finset.sum_congr rfl
            intro f _
            exact Finset.sum_comm
      _ = ∑ f : Fin k ↪ Fin n, ∑ j : Fin k, A.prob (LinearOrder.lift' f.toFun f.injective) j := by
            apply Finset.sum_congr rfl
            intro f _
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_ite_eq]
            simp
      _ = ∑ f : Fin k ↪ Fin n, (1:ℝ) := by
            apply Finset.sum_congr rfl
            intro f _
            exact A.total _
      _ = (Fintype.card (Fin k ↪ Fin n) : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Finset.sum_div, hsum, div_self hNne]
  · intro hn L
    set m := linearOrderMin hn L with hm
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hgoal : ((k : ℝ) * p) / (n : ℝ) ≤
        (∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
          (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0)) /
          (Fintype.card (Fin k ↪ Fin n) : ℝ) := by
      have hfv : ∀ f ∈ Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f),
          p ≤ ∑ j : Fin k, (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) := by
        intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨j0, hj0⟩ := hf
        have hv : (∑ j : Fin k, (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0))
            = A.prob (LinearOrder.lift' f.toFun f.injective) j0 := by
          have h := Finset.sum_eq_single (s := Finset.univ)
            (f := fun j => if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) j0 ?_ ?_
          · simpa [hj0] using h
          · intro b _ hb
            have hbm : f b ≠ m := fun hb' => hb (f.injective (hb'.trans hj0.symm))
            simp [hbm]
          · intro h; exact absurd (Finset.mem_univ j0) h
        rw [hv]
        have hmin := lift_linear_order_min_eq hk hn L f j0 (hj0.trans hm)
        have hprob := hp (LinearOrder.lift' f.toFun f.injective)
        rw [comparison_algorithm_success_prob, hmin] at hprob
        exact hprob
      have h1 : ∑ f ∈ Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f), p
          ≤ ∑ f ∈ Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f),
              ∑ j : Fin k, (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) :=
        Finset.sum_le_sum hfv
      have h2 : ∑ f ∈ Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f), p
          = ((Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card : ℝ) * p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ∑ f ∈ Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f),
              ∑ j : Fin k, (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0)
          ≤ ∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
              (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro f _ _
          apply Finset.sum_nonneg
          intro j _
          split_ifs
          · exact A.nonneg _ _
          · exact le_refl 0
      have hsum_ge : ((Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card : ℝ) * p
          ≤ ∑ f : Fin k ↪ Fin n, ∑ j : Fin k,
              (if f j = m then A.prob (LinearOrder.lift' f.toFun f.injective) j else 0) := by
        linarith
      have hcardval : ((Finset.univ.filter (fun f : Fin k ↪ Fin n => m ∈ Set.range f)).card : ℝ) =
          (Fintype.card (Fin k ↪ Fin n) : ℝ) * ((k : ℝ) / (n : ℝ)) := by
        have hc := embedding_range_contains_fraction hk hkn m
        rw [div_eq_iff hNne] at hc
        rw [hc]; ring
      have hdiv := div_le_div_of_nonneg_right hsum_ge (le_of_lt hNpos)
      rw [hcardval] at hdiv
      have heq : ((Fintype.card (Fin k ↪ Fin n) : ℝ) * ((k : ℝ) / (n : ℝ)) * p) /
          (Fintype.card (Fin k ↪ Fin n) : ℝ) = ((k : ℝ) * p) / (n : ℝ) := by
        field_simp
      rw [heq] at hdiv
      linarith
    simpa [comparison_algorithm_success_prob, hm] using hgoal
