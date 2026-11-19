import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionFixedEndpoints

/-!
# path_selection_endpoint_sets

Topic: combinatorics   Node: e80e69af9ac4

Provenance: helper lemma. Endpoint-list criterion for the half-edge path reduction in OP-874.

For equal-size finite palettes along a path and nonempty allowed starting set A, an endpoint-constrained selection exists precisely when an allowed final color is either also allowed initially or disappears from some palette along the path.
-/

theorem path_selection_endpoint_sets {Ω : Type*} [DecidableEq Ω]
    (P : ℕ → Finset Ω) (hcard : ∀ i, (P i).card = (P (i+1)).card)
    (n : ℕ) (A B : Finset Ω) (hA : A.Nonempty)
    (hA0 : A ⊆ P 0) (hBn : B ⊆ P n) :
    (∃ f : ℕ → Ω, f 0 ∈ A ∧ f n ∈ B ∧ (∀ i ≤ n, f i ∈ P i) ∧
      (∀ i < n, f (i+1) ∈ P i → f (i+1) = f i)) ↔
    (∃ y ∈ B, y ∈ A ∨ ∃ i ≤ n, y ∉ P i) := by
  classical
  constructor
  · rintro ⟨f, hfA, hfB, hfmem, hfstep⟩
    refine ⟨f n, hfB, ?_⟩
    by_cases h : f n ∈ A
    · exact Or.inl h
    · right
      by_contra hnone
      have hall : ∀ i ≤ n, f n ∈ P i := by
        intro i hi
        by_contra hni
        exact hnone ⟨i, hi, hni⟩
      have hxy : f 0 = f n :=
        (path_selection_fixed_endpoints P hcard (f 0) (hA0 hfA) n (f n)
          (hBn hfB)).1 ⟨f, rfl, rfl, hfmem, hfstep⟩ hall
      exact h (hxy ▸ hfA)
  · rintro ⟨y, hyB, hy⟩
    obtain ⟨a, ha⟩ := hA
    rcases hy with hyA | ⟨i, hi, hni⟩
    · obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ :=
        (path_selection_fixed_endpoints P hcard y (hA0 hyA) n y (hBn hyB)).2 (by intro; rfl)
      exact ⟨f, by simpa [hf0] using hyA, by simpa [hfn] using hyB, hfmem, hfstep⟩
    · obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ :=
        (path_selection_fixed_endpoints P hcard a (hA0 ha) n y (hBn hyB)).2
          (by intro hall; exact (hni (hall i hi)).elim)
      exact ⟨f, by simpa [hf0] using ha, by simpa [hfn] using hyB, hfmem, hfstep⟩
