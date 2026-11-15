import AFTD.Prelude
import AFTD.Kb.Tcs.OneStronglyEuclideanUnionTwoSetsDistortion

/-!
# ose_universal_extension_of_isometry_extension

Topic: algorithms   Node: de73cd689f88

Provenance: helper lemma. arXiv:2611.08546, Section 3.2; Hilbert-valued nonexpanding extension

If a map from a metric space into a real inner-product space extends a prescribed core map with Lipschitz constant L, then every nonexpanding Hilbert-valued map on that core extends to the whole metric space with Lipschitz constant L.
-/

theorem ose_universal_extension_of_isometry_extension (A X E : Type) [MetricSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : A → E) (i : A → X) (L : ℝ) (f : X → E)
    (hfix : ∀ a, f (i a)=u a) (hf : ∀ x y, dist (f x) (f y) ≤ L*dist x y)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : A → H) (hg : ∀ a b, dist (g a) (g b) ≤ dist (u a) (u b)) :
    ∃ F : X → H, (∀ a, F (i a)=g a) ∧ ∀ x y, dist (F x) (F y) ≤ L*dist x y := by
  let G : Set (E × H) := Set.range (fun a => (u a,g a))
  have hG : ∀ p ∈ G, ∀ p' ∈ G, ‖p.2-p'.2‖ ≤ (1 : ℝ)*‖p.1-p'.1‖ := by
    rintro p ⟨a,rfl⟩ p' ⟨b,rfl⟩
    simpa only [one_mul, ← dist_eq_norm] using hg a b
  obtain ⟨T,hT,hLip⟩ := ose_kirszbraun (1 : ℝ) (by norm_num) G hG
  refine ⟨fun x => T (f x), ?_, ?_⟩
  · intro a
    change T (f (i a)) = g a
    rw [hfix a]
    exact hT (u a,g a) ⟨a,rfl⟩
  · intro x y
    have h := hLip (f x) (f y)
    simp only [one_mul, ← dist_eq_norm] at h
    exact le_trans h (hf x y)
