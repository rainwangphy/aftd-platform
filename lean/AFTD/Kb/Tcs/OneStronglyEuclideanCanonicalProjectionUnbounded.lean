import AFTD.Prelude
import AFTD.Kb.Tcs.IsOneStronglyEuclidean

/-!
# one_strongly_euclidean_canonical_projection_unbounded

Topic: algorithms   Node: e1790b7797ea

Provenance: helper lemma. OP-1304, arXiv:2611.08546; obstruction to using the canonical one-point projections as uniformly Lipschitz maps.

For any real L there is a metric on four points covered by two 1-strongly Euclidean pairs {0,1} and {2,3}, with d(0,1)=d(2,3)=1, such that the canonical projections of 2 and 3 onto the affine line through the first pair are more than L apart. The projection difference is computed from the squared distances to 0 and 1.
-/

set_option maxHeartbeats 2000000

noncomputable def op1304ProjectionMetric (r : ℝ) (hr : 1 ≤ r) : MetricSpace (Fin 4) where
  dist a b := if a = b then 0 else if a.val / 2 = b.val / 2 then 1 else if a.val % 2 = b.val % 2 then r else r + 1
  dist_self := by intro a; simp
  dist_comm := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num
  dist_triangle := by
    intro a b c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num <;> linarith
  eq_of_dist_eq_zero := by
    intro a b h
    fin_cases a <;> fin_cases b <;> norm_num at * <;> linarith


theorem op1304ProjectionA (r : ℝ) (hr : 1 ≤ r) :
    letI := op1304ProjectionMetric r hr
    IsOneStronglyEuclidean ({0,1} : Set (Fin 4)) := by
  letI := op1304ProjectionMetric r hr
  intro x
  refine ⟨ℝ, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun a => if a.val = 0 then 0 else if a.val = 1 then 1 else if a.val = 2 then -r else r + 1
  · rw [isometry_iff_dist_eq]
    intro a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    change dist _ _ = (if a = b then 0 else if a.val / 2 = b.val / 2 then 1 else if a.val % 2 = b.val % 2 then r else r + 1)
    fin_cases x <;> fin_cases a <;> fin_cases b <;>
      norm_num [Real.dist_eq] at * <;> split_ifs at * <;> simp_all [Fin.ext_iff] <;> norm_num at * <;> (first | linarith [abs_nonneg r] | (rw [abs_of_nonneg (by linarith)]; linarith) | (rw [abs_of_nonpos (by linarith)]; linarith))

theorem op1304ProjectionB (r : ℝ) (hr : 1 ≤ r) :
    letI := op1304ProjectionMetric r hr
    IsOneStronglyEuclidean ({2,3} : Set (Fin 4)) := by
  letI := op1304ProjectionMetric r hr
  intro x
  refine ⟨ℝ, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun a => if a.val = 2 then 0 else if a.val = 3 then 1 else if a.val = 0 then -r else r + 1
  · rw [isometry_iff_dist_eq]
    intro a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    change dist _ _ = (if a = b then 0 else if a.val / 2 = b.val / 2 then 1 else if a.val % 2 = b.val % 2 then r else r + 1)
    fin_cases x <;> fin_cases a <;> fin_cases b <;>
      norm_num [Real.dist_eq] at * <;> split_ifs at * <;> simp_all [Fin.ext_iff] <;> norm_num at * <;> (first | linarith [abs_nonneg r] | (rw [abs_of_nonneg (by linarith)]; linarith) | (rw [abs_of_nonpos (by linarith)]; linarith))

theorem one_strongly_euclidean_canonical_projection_unbounded : ∀ L : ℝ,
  ∃ m : MetricSpace (Fin 4), letI := m
    IsOneStronglyEuclidean ({0,1} : Set (Fin 4)) ∧
    IsOneStronglyEuclidean ({2,3} : Set (Fin 4)) ∧
    dist (0 : Fin 4) 1 = 1 ∧ dist (2 : Fin 4) 3 = 1 ∧
    L < |((dist (2 : Fin 4) 0)^2 - (dist (2 : Fin 4) 1)^2) / 2 -
         ((dist (3 : Fin 4) 0)^2 - (dist (3 : Fin 4) 1)^2) / 2| := by
  intro L
  let r : ℝ := |L| + 2
  have hr : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg L]
  refine ⟨op1304ProjectionMetric r hr, op1304ProjectionA r hr, op1304ProjectionB r hr, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · change L < |(r^2 - (r+1)^2)/2 - ((r+1)^2 - r^2)/2|
    rw [abs_of_nonpos (by nlinarith)]
    dsimp [r]
    nlinarith [le_abs_self L]
