import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# fin_intervals_intersection_nonempty_of_pairwise_inter

Topic: graphs   Node: bc61349aa3a5

Provenance: helper lemma. folklore

Let L be a natural number and let ι be a finite nonempty index type. Let [a i, b i] for i : ι be a family of nonempty closed intervals in Fin L (so a i ≤ b i for all i). If every pair of intervals intersects (for all i, j in ι, there exists k : Fin L with a i ≤ k ≤ b i and a j ≤ k ≤ b j), then there exists a common element k : Fin L contained in every interval (a i ≤ k ≤ b i for all i : ι).
-/

/-- A finite nonempty family of pairwise intersecting closed intervals in Fin L has a nonempty total intersection. -/
theorem fin_intervals_intersection_nonempty_of_pairwise_inter {L : ℕ} {ι : Type*} [Finite ι] [Nonempty ι]
    (a b : ι → Fin L) (hab : ∀ i, a i ≤ b i)
    (h_inter : ∀ i j, ∃ k : Fin L, a i ≤ k ∧ k ≤ b i ∧ a j ≤ k ∧ k ≤ b j) :
    ∃ k : Fin L, ∀ i, a i ≤ k ∧ k ≤ b i := by
  have _ := hab
  cases nonempty_fintype ι
  refine ⟨Finset.univ.sup' Finset.univ_nonempty a, fun i => ⟨Finset.le_sup' a (Finset.mem_univ i), ?_⟩⟩
  apply Finset.sup'_le
  intro j _
  obtain ⟨k', hj, -, -, hi⟩ := h_inter j i
  exact le_trans hj hi
