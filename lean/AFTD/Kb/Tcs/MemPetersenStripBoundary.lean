import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStrip
import AFTD.Kb.Tcs.PetersenStripBoundary
import AFTD.Kb.Tcs.PetersenStripVertex

/-!
# mem_petersen_strip_boundary

Topic: graphs   Node: dd277a740b9b

Provenance: helper lemma. scout/2610-24059-sharp-zero-forcing-numbers-for-the-generalized-petersen-gra.md:191

For a natural number k, a finite vertex set S : Finset PetersenStripVertex, and a vertex w : PetersenStripVertex, w ∈ petersen_strip_boundary k S if and only if w ∉ S and there exists some u ∈ S such that (petersen_strip k).Adj u w.
-/

/-- Characterization of the external vertex boundary in the generalized Petersen strip. -/
theorem mem_petersen_strip_boundary (k : ℕ) (S : Finset PetersenStripVertex) (w : PetersenStripVertex) : w ∈ petersen_strip_boundary k S ↔ w ∉ S ∧ ∃ u ∈ S, (petersen_strip k).Adj u w := by
  dsimp only [petersen_strip_boundary]
  rw [Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨u, huS, huw⟩, hwS⟩
    refine ⟨hwS, u, huS, ?_⟩
    rcases u with i | i <;> rcases w with j | j
    · dsimp [petersen_strip] at *
      simp only [Finset.mem_insert, Finset.mem_singleton] at huw
      simp at huw ⊢
      exact huw
    · dsimp [petersen_strip] at *
      simp only [Finset.mem_insert, Finset.mem_singleton] at huw
      simp at huw ⊢
      exact huw
    · dsimp [petersen_strip] at *
      split_ifs at huw with hk
      · simp only [Finset.mem_singleton] at huw
        simp at huw ⊢
        exact huw
      · simp only [Finset.mem_insert, Finset.mem_singleton] at huw
        simp at huw ⊢
        exact huw
    · dsimp [petersen_strip] at *
      split_ifs at huw with hk
      · simp only [Finset.mem_singleton] at huw
        contradiction
      · simp only [Finset.mem_insert, Finset.mem_singleton] at huw
        simp [hk] at huw ⊢
        exact huw
  · rintro ⟨hwS, u, huS, huw⟩
    refine ⟨⟨u, huS, ?_⟩, hwS⟩
    rcases u with i | i <;> rcases w with j | j
    · dsimp [petersen_strip] at *
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simp at huw ⊢
      exact huw
    · dsimp [petersen_strip] at *
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simp at huw ⊢
      exact huw
    · dsimp [petersen_strip] at *
      split_ifs with hk
      · simp only [Finset.mem_singleton]
        simp at huw ⊢
        exact huw
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        simp at huw ⊢
        exact huw
    · dsimp [petersen_strip] at *
      split_ifs with hk
      · subst hk
        simp at huw
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        simp [hk] at huw ⊢
        exact huw
