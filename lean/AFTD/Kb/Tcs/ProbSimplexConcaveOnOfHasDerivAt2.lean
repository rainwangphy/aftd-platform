import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# prob_simplex_concaveOn_of_hasDerivAt2

Topic: information   Node: 0427ecc884f7

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

A function on the open probability simplex {r : ∀x, 0 < r x, Σ r = 1} is concave if, at every point r of it and in every direction v with Σ v = 0, t ↦ F(r + t v) has derivative D1 r v at 0, t ↦ D1(r + t v) v has derivative D2 r v at 0, and D2 r v ≤ 0 (second-derivative test along segments).
-/

theorem prob_simplex_concaveOn_of_hasDerivAt2 {X : Type*} [Fintype X] (Φ : (X → ℝ) → ℝ)
    (D1 D2 : (X → ℝ) → (X → ℝ) → ℝ)
    (h1 : ∀ r : X → ℝ, (∀ x, 0 < r x) → ∑ x, r x = 1 → ∀ v : X → ℝ, ∑ x, v x = 0 →
      HasDerivAt (fun t : ℝ => Φ (r + t • v)) (D1 r v) 0)
    (h2 : ∀ r : X → ℝ, (∀ x, 0 < r x) → ∑ x, r x = 1 → ∀ v : X → ℝ, ∑ x, v x = 0 →
      HasDerivAt (fun t : ℝ => D1 (r + t • v) v) (D2 r v) 0)
    (h3 : ∀ r : X → ℝ, (∀ x, 0 < r x) → ∑ x, r x = 1 → ∀ v : X → ℝ, ∑ x, v x = 0 →
      D2 r v ≤ 0) :
    ConcaveOn ℝ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} Φ := by
  have hS : Convex ℝ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} := by
    intro a ha b hb α β hα hβ hαβ
    refine ⟨fun x => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hα.lt_or_eq with h | h
      · have := ha.1 x; have := hb.1 x; positivity
      · subst h
        have : β = 1 := by linarith
        subst this; simp [hb.1 x]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha.2, hb.2]
      linarith
  refine ⟨hS, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  set v : X → ℝ := b - a with hvdef
  have hv : ∑ x, v x = 0 := by simp [v, Finset.sum_sub_distrib, ha.2, hb.2]
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1,
      a + t • v ∈ {r : X → ℝ | (∀ x, 0 < r x) ∧ ∑ x, r x = 1} := by
    intro t ht
    have : a + t • v = (1 - t) • a + t • b := by
      funext x; simp [v]; ring
    rw [this]; exact hS ha hb (by linarith [ht.2]) ht.1 (by ring)
  set φ : ℝ → ℝ := fun t => Φ (a + t • v) with hφ
  set ψ : ℝ → ℝ := fun t => D1 (a + t • v) v with hψ
  have shift : ∀ (Gv : (X → ℝ) → ℝ) (d t : ℝ),
      HasDerivAt (fun s : ℝ => Gv ((a + t • v) + s • v)) d 0 →
      HasDerivAt (fun s : ℝ => Gv (a + s • v)) d t := by
    intro Gv d t h
    have hg : HasDerivAt (fun s : ℝ => Gv ((a + t • v) + s • v)) d (t - t) := by
      rw [sub_self]; exact h
    have hh : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id' t).sub_const t
    have := HasDerivAt.comp (h := fun s : ℝ => s - t) t hg hh
    rw [mul_one] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp]
    congr 1
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hd1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    obtain ⟨hp, hs⟩ := hseg t ht
    exact shift Φ _ t (h1 _ hp hs v hv)
  have hd2 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (D2 (a + t • v) v) t := by
    intro t ht
    obtain ⟨hp, hs⟩ := hseg t ht
    exact shift (fun r => D1 r v) _ t (h2 _ hp hs v hv)
  have hint : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  have hcc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    refine concaveOn_of_deriv2_nonpos (convex_Icc 0 1)
      (fun t ht => (hd1 t ht).continuousAt.continuousWithinAt) ?_ ?_ ?_
    · rw [hint]; intro t ht
      exact (hd1 t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro t ht
      have heq : deriv φ =ᶠ[nhds t] ψ := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact (hd1 s (Set.Ioo_subset_Icc_self hs)).deriv
      exact ((hd2 t (Set.Ioo_subset_Icc_self ht)).congr_of_eventuallyEq
        heq).differentiableAt.differentiableWithinAt
    · rw [hint]; intro t ht
      have heq : deriv φ =ᶠ[nhds t] ψ := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact (hd1 s (Set.Ioo_subset_Icc_self hs)).deriv
      rw [Function.iterate_succ, Function.iterate_one, Function.comp,
        ((hd2 t (Set.Ioo_subset_Icc_self ht)).congr_of_eventuallyEq heq).deriv]
      obtain ⟨hp, hs⟩ := hseg t (Set.Ioo_subset_Icc_self ht)
      exact h3 _ hp hs v hv
  have := hcc.2 (x := 0) (y := 1) (by simp) (by simp) hα hβ hαβ
  simp only [φ, zero_smul, add_zero, one_smul, smul_eq_mul, mul_zero, mul_one, zero_add] at this
  have e1 : a + v = b := by funext x; simp [v]
  have e2 : a + β • v = α • a + β • b := by
    funext x; simp [v]; rw [show α = 1 - β by linarith]; ring
  rw [e1, e2] at this
  exact this
