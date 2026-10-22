import AFTD.Prelude
import AFTD.Kb.Tcs.BackIdentityMatrix
import AFTD.Kb.Tcs.MulBackIdentityMatrixApply
import AFTD.Kb.Tcs.BorderedGoethalsSeidelMatrix
import AFTD.Kb.Tcs.GoethalsSeidelArray

/-!
# bordered_goethals_seidel_matrix_entries

Topic: combinatorics   Node: 4bd32c6fae5f

Provenance: helper lemma. step of arXiv:2610.27175 Theorem 5 (the matrix is a {±1}-matrix)

If a, b, c, d : Fin m → ℤ take only the values 1 and -1, every entry of the bordered Goethals-Seidel matrix built from their circulants is 1 or -1.
-/

theorem bordered_goethals_seidel_matrix_entries {m : ℕ} (a b c d : Fin m → ℤ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hd : ∀ i, d i = 1 ∨ d i = -1) (i j : Fin 4 ⊕ Fin 4 × Fin m) :
    bordered_goethals_seidel_matrix (Matrix.circulant a) (Matrix.circulant b)
      (Matrix.circulant c) (Matrix.circulant d) i j = 1 ∨
    bordered_goethals_seidel_matrix (Matrix.circulant a) (Matrix.circulant b)
      (Matrix.circulant c) (Matrix.circulant d) i j = -1 := by
  have hcirc : ∀ v : Fin m → ℤ, (∀ i, v i = 1 ∨ v i = -1) →
      ∀ i j, Matrix.circulant v i j = 1 ∨ Matrix.circulant v i j = -1 :=
    fun v hv i j => hv (i - j)
  have hneg : ∀ X : Matrix (Fin m) (Fin m) ℤ, (∀ i j, X i j = 1 ∨ X i j = -1) →
      ∀ i j, (-X) i j = 1 ∨ (-X) i j = -1 := by
    intro X hX i j
    rw [Matrix.neg_apply]
    rcases hX i j with h | h <;> rw [h] <;> simp
  have hR : ∀ X : Matrix (Fin m) (Fin m) ℤ, (∀ i j, X i j = 1 ∨ X i j = -1) →
      ∀ i j, (X * back_identity_matrix m) i j = 1 ∨ (X * back_identity_matrix m) i j = -1 := by
    intro X hX i j
    rw [mul_back_identity_matrix_apply]
    exact hX i j.rev
  have hT : ∀ X : Matrix (Fin m) (Fin m) ℤ, (∀ i j, X i j = 1 ∨ X i j = -1) →
      ∀ i j, X.transpose i j = 1 ∨ X.transpose i j = -1 :=
    fun X hX i j => hX j i
  have hA := hcirc a ha
  have hB := hcirc b hb
  have hC := hcirc c hc
  have hD := hcirc d hd
  rcases i with r | ⟨p, i⟩ <;> rcases j with r' | ⟨q, j⟩
  · fin_cases r <;> fin_cases r' <;> simp [bordered_goethals_seidel_matrix]
  · fin_cases r <;> fin_cases q <;> simp [bordered_goethals_seidel_matrix]
  · fin_cases p <;> fin_cases r' <;> simp [bordered_goethals_seidel_matrix]
  · fin_cases p <;> fin_cases q <;>
      first
        | exact hA i j
        | exact hR _ hB i j | exact hR _ hC i j | exact hR _ hD i j
        | exact hneg _ (hR _ hB) i j | exact hneg _ (hR _ hC) i j | exact hneg _ (hR _ hD) i j
        | exact hR _ (hT _ hB) i j | exact hR _ (hT _ hC) i j | exact hR _ (hT _ hD) i j
        | exact hneg _ (hR _ (hT _ hB)) i j | exact hneg _ (hR _ (hT _ hC)) i j
        | exact hneg _ (hR _ (hT _ hD)) i j
