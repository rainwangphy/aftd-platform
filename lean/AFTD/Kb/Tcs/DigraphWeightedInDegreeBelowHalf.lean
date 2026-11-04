import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_weighted_in_degree_below_half

Topic: graphs   Node: 2a8b39c43fe5

Provenance: helper lemma. Elementary weighted averaging over oriented vertex pairs; no novelty is claimed.

In a finite nonempty oriented graph, some vertex minimizes the weight of its in-neighborhood, and that in-neighborhood has at most half the total nonnegative integer weight.
-/

theorem digraph_weighted_in_degree_below_half
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Digraph α) [DecidableRel D.Adj]
    (horient : ∀ u v, D.Adj u v → ¬ D.Adj v u) (w : α → ℕ) :
    ∃ v, (∀ x, (∑ u ∈ Finset.univ.filter (fun u => D.Adj u v), w u) ≤
      ∑ u ∈ Finset.univ.filter (fun u => D.Adj u x), w u) ∧
      2 * (∑ u ∈ Finset.univ.filter (fun u => D.Adj u v), w u) ≤
        ∑ u ∈ Finset.univ, w u := by
  classical
  let W : ℕ := ∑ u, w u
  let score : α → ℕ := fun v => ∑ u ∈ Finset.univ.filter (fun u => D.Adj u v), w u
  let F : α → α → ℕ := fun u v => if D.Adj u v then w u * w v else 0
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image Finset.univ score Finset.univ_nonempty
  have hpair : ∀ u v, F u v + F v u ≤ w u * w v := by
    intro u v
    by_cases huv : D.Adj u v
    · have hvu := horient u v huv
      simp [F, huv, hvu]
    · by_cases hvu : D.Adj v u
      · simp [F, huv, hvu, Nat.mul_comm]
      · simp [F, huv, hvu]
  have hdouble : (∑ u, ∑ v, (F u v + F v u)) ≤
      ∑ u, ∑ v, w u * w v := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact hpair u v
  have hsym : (∑ u, ∑ v, F v u) = ∑ u, ∑ v, F u v := by
    exact Finset.sum_comm
  have hprod : (∑ u, ∑ v, w u * w v) = W * W := by
    dsimp [W]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hF : (∑ u, ∑ v, F u v) = ∑ v, w v * score v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    simp [F, score, Finset.mul_sum, Finset.sum_filter, Nat.mul_comm]
  have hbound : 2 * (∑ v, w v * score v) ≤ W * W := by
    simp only [Finset.sum_add_distrib] at hdouble
    rw [hsym, hprod] at hdouble
    simp only [hF] at hdouble
    omega
  have hminsum : W * score s ≤ ∑ v, w v * score v := by
    calc
      W * score s = ∑ v, w v * score s := by simp [W, Finset.sum_mul]
      _ ≤ ∑ v, w v * score v := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.mul_le_mul_left _ (hmin v hv)
  by_cases hW : W = 0
  · refine ⟨s, ?_, ?_⟩
    · intro x
      exact hmin x (Finset.mem_univ x)
    · have hscore : score s ≤ W := by
        simpa [score, W] using
          (Finset.sum_le_sum_of_subset (f := w) (Finset.filter_subset (fun u => D.Adj u s) Finset.univ))
      have : 2 * score s ≤ W := by omega
      simpa [score, W] using this
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hW
    have hkey : W * (2 * score s) ≤ W * W := by nlinarith
    have hscore : 2 * score s ≤ W := Nat.le_of_mul_le_mul_left hkey hWpos
    refine ⟨s, ?_, ?_⟩
    · intro x
      exact hmin x (Finset.mem_univ x)
    · simpa [score, W] using hscore
