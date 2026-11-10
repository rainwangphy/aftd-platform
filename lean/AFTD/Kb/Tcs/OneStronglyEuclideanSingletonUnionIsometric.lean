import AFTD.Prelude
import AFTD.Kb.Tcs.IsOneStronglyEuclidean
import AFTD.Kb.Tcs.EmbedsIntoHilbertWithDistortion

/-!
# one_strongly_euclidean_singleton_union_isometric

Topic: algorithms   Node: fb6ba0050300

Provenance: helper lemma. arXiv:2611.08546 Definition 1.1

If a nonempty metric space X is the union of a single subset U_0 that is 1-strongly Euclidean in X, then X embeds into a real Hilbert space with distortion at most 1 (isometrically).
-/

/-- Isometric embedding into Hilbert space for a single 1-strongly Euclidean set. -/
theorem one_strongly_euclidean_singleton_union_isometric.{u}
    (X : Type u) [MetricSpace X] [Nonempty X]
    (U : Fin 1 → Set X) (_hU : (⋃ i, U i) = Set.univ)
    (_hE : ∀ i, IsOneStronglyEuclidean (U i)) :
    EmbedsIntoHilbertWithDistortion X 1 := by
  have hU0 : U 0 = Set.univ := by
    have : (⋃ i, U i) = U 0 := by
      ext x
      simp
    rw [← this, _hU]
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  obtain ⟨H, nH, iH, cH, f, hf⟩ := _hE 0 x0
  let _ : NormedAddCommGroup H := nH
  let _ : InnerProductSpace ℝ H := iH
  let _ : CompleteSpace H := cH
  have h_mem : ∀ x : X, x ∈ U 0 ∪ {x0} := fun x => Or.inl (by rw [hU0]; exact Set.mem_univ x)
  let F : X → H := fun x => f ⟨x, h_mem x⟩
  refine ⟨H, nH, iH, cH, F, ?_⟩
  intro x y
  have h_dist : dist (F x) (F y) = dist x y := hf.dist_eq ⟨x, h_mem x⟩ ⟨y, h_mem y⟩
  rw [h_dist]
  simp
