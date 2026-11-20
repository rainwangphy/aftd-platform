import AFTD.Prelude
import AFTD.Kb.Tcs.CraigShellSize

/-!
# craig_shell_size_k_one

Topic: information   Node: 371f87761cb6

Provenance: formalization of a published result. Source: arXiv:2611.22441 Eq. (7)

For any prime p, the number of shortest nonzero vectors of Euclidean norm √2 in Craig's lattice A_{p-1}^1 is p * (p - 1).
-/

/-- For any prime p, the shortest vector shell size of Craig's lattice for k = 1 is p * (p - 1). -/
theorem craig_shell_size_k_one (p : ℕ) (hp : Nat.Prime p) : craig_shell_size p 1 = p * (p - 1) := by
  have _ := hp
  have h_card : (Finset.offDiag (Finset.univ : Finset (Fin p))).card = p * (p - 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib, mul_one]
  rw [← h_card]
  dsimp [craig_shell_size]
  symm
  apply Finset.card_bij (fun ⟨x, y⟩ _ => ({x}, {y}))
  · intro ⟨x, y⟩ hxy
    rw [Finset.mem_offDiag] at hxy
    dsimp at hxy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ, and_true,
      Finset.card_singleton, true_and]
    refine ⟨?_, fun r hr1 hr2 => by omega⟩
    rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact hxy.2.2
  · intro ⟨x1, y1⟩ _ ⟨x2, y2⟩ _ h
    injection h with h1 h2
    rw [Finset.singleton_inj] at h1 h2
    rw [h1, h2]
  · rintro ⟨S1, S2⟩ hS
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hS
    rcases hS with ⟨-, h1, h2, hdisj, -⟩
    rw [Finset.card_eq_one] at h1 h2
    rcases h1 with ⟨x, rfl⟩
    rcases h2 with ⟨y, rfl⟩
    refine ⟨⟨x, y⟩, ?_, rfl⟩
    rw [Finset.mem_offDiag]
    dsimp
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    intro hxy
    subst hxy
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton] at hdisj
    exact hdisj trivial
