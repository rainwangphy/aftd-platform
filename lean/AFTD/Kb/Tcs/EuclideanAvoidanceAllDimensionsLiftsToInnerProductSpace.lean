import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanAvoidsAp

/-!
# euclidean_avoidance_all_dimensions_lifts_to_inner_product_space

Topic: combinatorics   Node: bc3b53027add

Provenance: helper lemma. OP-1482; compactness reduction to one infinite-dimensional coloring

If every finite-dimensional real Euclidean space admits a two-coloring avoiding the specified false and true arithmetic progressions, then every real inner-product space admits such a coloring, with the same lengths and spacings.
-/

open Set

private theorem in931_finite_coloring_compactness
    (V I : Type*) (P : I → (V → Bool) → Prop) (support : I → Finset V)
    (hlocal : ∀ i f g, (∀ x ∈ support i, f x = g x) → (P i f ↔ P i g))
    (hfinite : ∀ s : Finset I, ∃ f, ∀ i ∈ s, P i f) :
    ∃ f, ∀ i, P i f := by
  classical
  have hclosed (i : I) : IsClosed {f : V → Bool | P i f} := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro f hf
    let U : Set (V → Bool) := ⋂ x ∈ support i, {g | g x = f x}
    have hU : IsOpen U := by
      apply isOpen_biInter_finset
      intro x hx
      change IsOpen {g : V → Bool | g x = f x}
      have hEval : Continuous (fun g : V → Bool => g x) := continuous_apply x
      have hS : IsOpen ({f x} : Set Bool) := isOpen_discrete _
      exact hS.preimage hEval
    have hfU : f ∈ U := by simp [U]
    apply Filter.mem_of_superset (hU.mem_nhds hfU)
    intro g hg hpg
    apply hf
    apply (hlocal i g f ?_).mp hpg
    intro x hx
    have := hg
    simp only [U, mem_iInter, mem_setOf_eq] at this
    exact this x hx
  have hn : (⋂ i : I, {f : V → Bool | P i f}).Nonempty := by
    apply CompactSpace.iInter_nonempty hclosed
    intro s
    obtain ⟨f, hf⟩ := hfinite s
    refine ⟨f, ?_⟩
    simpa only [mem_iInter, mem_setOf_eq] using hf
  obtain ⟨f, hf⟩ := hn
  exact ⟨f, by simpa only [mem_iInter, mem_setOf_eq] using hf⟩



private theorem in931_finite_dimensional_avoidance
    (r m : ℕ) (α β : ℝ)
    (h : ∀ n : ℕ, euclidean_avoids_ap n r α m β)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] :
    ∃ c : H → Bool,
      (¬ ∃ x v : H, ‖v‖ = α ∧ ∀ k : Fin r, c (x + (k.val : ℝ) • v) = false) ∧
      (¬ ∃ x v : H, ‖v‖ = β ∧ ∀ k : Fin m, c (x + (k.val : ℝ) • v) = true) := by
  classical
  let e := (stdOrthonormalBasis ℝ H).repr
  obtain ⟨c, hc0, hc1⟩ := h (Module.finrank ℝ H)
  refine ⟨fun x => c (e x), ?_, ?_⟩
  · rintro ⟨x, v, hv, hc⟩
    apply hc0
    refine ⟨e x, e v, ?_, ?_⟩
    · simpa [e] using hv
    · intro k
      simpa only [map_add, map_smul] using hc k
  · rintro ⟨x, v, hv, hc⟩
    apply hc1
    refine ⟨e x, e v, ?_, ?_⟩
    · simpa [e] using hv
    · intro k
      simpa only [map_add, map_smul] using hc k

theorem euclidean_avoidance_all_dimensions_lifts_to_inner_product_space (r m : ℕ) (α β : ℝ) (h : ∀ n : ℕ, euclidean_avoids_ap n r α m β) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : ∃ c : H → Bool, (¬ ∃ x v : H, ‖v‖ = α ∧ ∀ k : Fin r, c (x + (k.val : ℝ) • v) = false) ∧ (¬ ∃ x v : H, ‖v‖ = β ∧ ∀ k : Fin m, c (x + (k.val : ℝ) • v) = true) := by
  classical
  let I := (H × H) ⊕ (H × H)
  let pt : I → H × H := Sum.elim id id
  let support : I → Finset H := fun i =>
    { (pt i).1, (pt i).2 } ∪ match i with
    | Sum.inl p => Finset.univ.image fun k : Fin r => p.1 + (k.val : ℝ) • p.2
    | Sum.inr p => Finset.univ.image fun k : Fin m => p.1 + (k.val : ℝ) • p.2
  let P : I → (H → Bool) → Prop := fun i c =>
    match i with
    | Sum.inl p => ‖p.2‖ = α → ¬ ∀ k : Fin r, c (p.1 + (k.val : ℝ) • p.2) = false
    | Sum.inr p => ‖p.2‖ = β → ¬ ∀ k : Fin m, c (p.1 + (k.val : ℝ) • p.2) = true
  have hlocal : ∀ i f g, (∀ x ∈ support i, f x = g x) → (P i f ↔ P i g) := by
    intro i f g hfg
    rcases i with ⟨x, v⟩ | ⟨x, v⟩
    · have heq : ∀ k : Fin r, f (x + (k.val : ℝ) • v) = g (x + (k.val : ℝ) • v) := by
        intro k
        apply hfg
        simp [support, pt]
      dsimp [P]
      constructor <;> intro hh hv hc <;> apply hh hv <;> intro k
      · rw [heq]; exact hc k
      · rw [← heq]; exact hc k
    · have heq : ∀ k : Fin m, f (x + (k.val : ℝ) • v) = g (x + (k.val : ℝ) • v) := by
        intro k
        apply hfg
        simp [support, pt]
      dsimp [P]
      constructor <;> intro hh hv hc <;> apply hh hv <;> intro k
      · rw [heq]; exact hc k
      · rw [← heq]; exact hc k
  have hfinite : ∀ s : Finset I, ∃ f, ∀ i ∈ s, P i f := by
    intro s
    let S : Finset H := s.biUnion support
    let E : Submodule ℝ H := Submodule.span ℝ (S : Set H)
    letI : FiniteDimensional ℝ E := FiniteDimensional.span_finset ℝ S
    obtain ⟨c, hc0, hc1⟩ := in931_finite_dimensional_avoidance r m α β h E
    let C : H → Bool := fun x => if hx : x ∈ E then c ⟨x, hx⟩ else false
    have hC (x : E) : C x = c x := by simp [C, x.property]
    refine ⟨C, ?_⟩
    intro i hi
    have hx : (pt i).1 ∈ E := by
      apply Submodule.subset_span
      simp only [S, Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨i, hi, ?_⟩
      simp [support]
    have hv : (pt i).2 ∈ E := by
      apply Submodule.subset_span
      simp only [S, Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨i, hi, ?_⟩
      simp [support]
    rcases i with ⟨x, v⟩ | ⟨x, v⟩
    · dsimp [pt] at hx hv
      dsimp [P]
      intro hnorm hm
      apply hc0
      refine ⟨⟨x, hx⟩, ⟨v, hv⟩, ?_, ?_⟩
      · exact hnorm
      · intro k
        have hh := hm k
        change C (((⟨x, hx⟩ : E) + (k.val : ℝ) • ⟨v, hv⟩ : E) : H) = false at hh
        simpa only [hC] using hh
    · dsimp [pt] at hx hv
      dsimp [P]
      intro hnorm hm
      apply hc1
      refine ⟨⟨x, hx⟩, ⟨v, hv⟩, ?_, ?_⟩
      · exact hnorm
      · intro k
        have hh := hm k
        change C (((⟨x, hx⟩ : E) + (k.val : ℝ) • ⟨v, hv⟩ : E) : H) = true at hh
        simpa only [hC] using hh
  obtain ⟨c, hc⟩ := in931_finite_coloring_compactness H I P support hlocal hfinite
  refine ⟨c, ?_, ?_⟩
  · rintro ⟨x, v, hv, hm⟩
    exact hc (Sum.inl (x, v)) hv hm
  · rintro ⟨x, v, hv, hm⟩
    exact hc (Sum.inr (x, v)) hv hm
