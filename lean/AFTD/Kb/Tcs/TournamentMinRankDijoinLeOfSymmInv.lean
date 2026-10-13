import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentMinRank
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.TournamentOfSymmMatrix
import AFTD.Kb.Tcs.LowerOnesMatrix
import AFTD.Kb.Tcs.DigraphFlipByMatrix
import AFTD.Kb.Tcs.DigraphIsAcyclicOfRank
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# tournament_min_rank_dijoin_le_of_symm_inv

Topic: graphs   Node: d6d925a98b60

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Proposition 3.1. Stated here is the bound tmr(T(A) → T(B)) ≤ n; the proposition's remark that A is again invertible symmetric is not part of the statement (its symmetry is proved inside the proof).

Let B be an invertible symmetric n × n matrix over F₂, L the lower triangular all-ones matrix, and A = L B⁻¹ Lᵀ. Then the tournaments D₁ = T(A) and D₂ = T(B) satisfy tmr(D₁ → D₂) ≤ n.
-/

theorem tournament_min_rank_dijoin_le_of_symm_inv (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hB : B.IsSymm) (hdet : IsUnit B.det) :
    tournament_min_rank (digraph_dijoin
      (tournament_of_symm_matrix (lower_ones_matrix n * B⁻¹ * (lower_ones_matrix n).transpose))
      (tournament_of_symm_matrix B)) ≤ n := by
  have two : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hBinvT : (B⁻¹).transpose = B⁻¹ := by rw [Matrix.transpose_nonsing_inv, hB.eq]
  -- the diagonal blocks reverse exactly the arcs of `T(G)` that go downwards
  have diag : ∀ G : Matrix (Fin n) (Fin n) (ZMod 2), G.IsSymm → ∀ i j : Fin n,
      (G i j = 1 ∧ (tournament_of_symm_matrix G).Adj j i) ∨
        (G i j ≠ 1 ∧ (tournament_of_symm_matrix G).Adj i j) → (i : ℕ) < j := by
    intro G hG i j h
    have hs : G j i = G i j := by
      have := congrFun (congrFun hG.eq i) j
      simpa [Matrix.transpose_apply] using this
    simp only [tournament_of_symm_matrix, hs] at h
    rcases two (G i j) with h0 | h0 <;> simp [h0] at h <;>
      exact h
  have hdec : ∀ A : Matrix (Fin n) (Fin n) (ZMod 2), A.IsSymm →
      digraph_is_acyclic (digraph_flip_by_matrix
        (digraph_dijoin (tournament_of_symm_matrix A) (tournament_of_symm_matrix B))
        (Matrix.fromBlocks A (lower_ones_matrix n) (lower_ones_matrix n).transpose B)) := by
    intro A hA
    apply digraph_is_acyclic_of_rank _
      (Sum.elim (fun i : Fin n => 2 * (i : ℕ) + 1) (fun j : Fin n => 2 * (j : ℕ)))
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · have := diag A hA i j hxy
      simp only [Sum.elim_inl]
      omega
    · rcases hxy with ⟨_, h⟩ | ⟨h, _⟩
      · exact h.elim
      · have hji : ¬ j ≤ i := fun hji => h (by simp [Matrix.fromBlocks, lower_ones_matrix, hji])
        have hij : (i : ℕ) < j := by rw [not_le] at hji; exact hji
        simp only [Sum.elim_inl, Sum.elim_inr]
        omega
    · rcases hxy with ⟨h, _⟩ | ⟨_, h⟩
      · have hij : i ≤ j := by
          by_contra hc
          simp [Matrix.fromBlocks, lower_ones_matrix, hc] at h
        have hij' : (i : ℕ) ≤ j := hij
        simp only [Sum.elim_inl, Sum.elim_inr]
        omega
      · exact h.elim
    · have := diag B hB i j hxy
      simp only [Sum.elim_inr]
      omega
  -- the rank is at most `n`: the block matrix is `P B Pᵀ` with `P` of width `n`
  have hrank : ∀ L : Matrix (Fin n) (Fin n) (ZMod 2),
      (Matrix.fromBlocks (L * B⁻¹ * L.transpose) L L.transpose B).rank ≤ n := by
    intro L
    have hMP : Matrix.fromBlocks (L * B⁻¹ * L.transpose) L L.transpose B =
        Matrix.fromRows (L * B⁻¹) 1 * B * (Matrix.fromRows (L * B⁻¹) 1).transpose := by
      rw [Matrix.fromRows_mul, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
      congr 1
      · rw [Matrix.mul_assoc L B⁻¹ B, Matrix.nonsing_inv_mul B hdet, Matrix.mul_one,
          Matrix.transpose_mul, hBinvT, Matrix.mul_assoc]
      · rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul B hdet,
          Matrix.mul_one]
      · rw [Matrix.one_mul, Matrix.transpose_mul, hBinvT, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv B hdet, Matrix.one_mul]
      · rw [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    rw [hMP]
    calc _ ≤ (Matrix.fromRows (L * B⁻¹) 1 * B).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (Matrix.fromRows (L * B⁻¹) (1 : Matrix (Fin n) (Fin n) (ZMod 2))).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  have hAs : (lower_ones_matrix n * B⁻¹ * (lower_ones_matrix n).transpose).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBinvT,
      Matrix.mul_assoc]
  have hMs : (Matrix.fromBlocks (lower_ones_matrix n * B⁻¹ * (lower_ones_matrix n).transpose)
      (lower_ones_matrix n) (lower_ones_matrix n).transpose B).IsSymm :=
    Matrix.IsSymm.fromBlocks hAs rfl hB
  exact le_trans (Nat.sInf_le ⟨_, hMs, hdec _ hAs, rfl⟩) (hrank _)
