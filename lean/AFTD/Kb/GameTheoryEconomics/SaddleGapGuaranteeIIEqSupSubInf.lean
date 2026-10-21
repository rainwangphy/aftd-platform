import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SaddleGapGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGamePayoffAgainstRow

/-!
# saddle_gap_guarantee_II_eq_sup_sub_inf

Topic: equilibria   Node: fe05b45a8e2c

Provenance: helper lemma. arXiv:2610.25524, Eq (4.1)

For a positive natural number n with `[NeZero n]`, an n-by-n real matrix A : Matrix (Fin n) (Fin n) ℝ, and a strategy vector x : stdSimplex ℝ (Fin n), Player II's guarantee `(saddle_gap_game A).guarantee_II x` in the saddle-gap game equals `Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A x.val i) - Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j)`.
-/

lemma saddle_gap_guarantee_II_eq_sup_sub_inf_aux_sup_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ) :
    (Finset.univ : Finset (ι × κ)).sup' Finset.univ_nonempty (fun p => f p.1 - g p.2) =
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty f -
        (Finset.univ : Finset κ).inf' Finset.univ_nonempty g := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro p _
    have h1 : f p.1 ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty f :=
      Finset.le_sup' f (Finset.mem_univ _)
    have h2 : (Finset.univ : Finset κ).inf' Finset.univ_nonempty g ≤ g p.2 :=
      Finset.inf'_le g (Finset.mem_univ _)
    linarith
  · have key : (Finset.univ : Finset ι).sup' Finset.univ_nonempty f ≤
        (Finset.univ : Finset (ι × κ)).sup' Finset.univ_nonempty (fun p => f p.1 - g p.2) +
          (Finset.univ : Finset κ).inf' Finset.univ_nonempty g := by
      rw [Finset.sup'_le_iff]
      intro i _
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := κ)) g
      have h3 : f i - g j₀ ≤
          (Finset.univ : Finset (ι × κ)).sup' Finset.univ_nonempty (fun p => f p.1 - g p.2) :=
        Finset.le_sup' (fun p : ι × κ => f p.1 - g p.2) (Finset.mem_univ (i, j₀))
      linarith
    linarith

/-- Player II's guarantee against column strategy x in the saddle-gap game equals the maximum row payoff minus the minimum column payoff. -/
lemma saddle_gap_guarantee_II_eq_sup_sub_inf {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : stdSimplex ℝ (Fin n)) :
    (saddle_gap_game A).guarantee_II x =
      Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A x.val i) -
      Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j) := by
  have key : ∀ p : Fin n × Fin n,
      (saddle_gap_game A).Ei p x = Matrix.mulVec A x.val p.1 - Matrix.vecMul x.val A p.2 := by
    intro p
    obtain ⟨i, j⟩ := p
    simp only [MatrixGame.Ei, MatrixGame.payoffAgainstRow, saddle_gap_game, dotProduct, Matrix.mulVec,
      Matrix.vecMul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm (x.val k) (A i k)
  unfold MatrixGame.guarantee_II
  simp only [key]
  exact saddle_gap_guarantee_II_eq_sup_sub_inf_aux_sup_prod
    (fun i => Matrix.mulVec A x.val i) (fun j => Matrix.vecMul x.val A j)
