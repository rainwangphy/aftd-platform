import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicMatrixFourier

/-!
# cyclic_matrix_fourier_compl_adjMatrix

Topic: combinatorics   Node: bef2ce378850

Provenance: helper lemma. arXiv:2610.31807 Proposition 4.9 -- Additive energy and Fourier complexity of graphs

For any simple graph G on ZMod N, the two-dimensional cyclic Fourier transform of the complement graph's adjacency matrix at (m,n) is equal to (if m = 0 and n = 0 then N else 0) - (if m + n = 0 then 1 else 0) minus the 2D cyclic Fourier transform of G's adjacency matrix at (m,n).
-/

open scoped BigOperators

private noncomputable def cyclic_matrix_fourier_compl_adjMatrix_char (N : ℕ) [NeZero N] (k : ZMod N) :
    AddChar (ZMod N) ℂ where
  toFun x := ZMod.stdAddChar (-(k * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [mul_add, neg_add, AddChar.map_add_eq_mul]

private lemma cyclic_matrix_fourier_compl_adjMatrix_char_mem (N : ℕ) [NeZero N] (k x : ZMod N) :
    cyclic_matrix_fourier_compl_adjMatrix_char N k x = ZMod.stdAddChar (-(k * x)) := rfl

private lemma cyclic_matrix_fourier_compl_adjMatrix_exp_eq_stdAddChar_neg (N : ℕ) [NeZero N]
    (s : ZMod N) :
    Complex.exp (-2 * Real.pi * Complex.I * ((s.val : ℂ) / (N : ℂ))) = ZMod.stdAddChar (-s) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_neg]
  congr 1
  ring

private lemma cyclic_matrix_fourier_compl_adjMatrix_char_ne_one (N : ℕ) [NeZero N] (k : ZMod N)
    (hk : k ≠ 0) : cyclic_matrix_fourier_compl_adjMatrix_char N k ≠ 1 := by
  intro h
  have h1 : ZMod.stdAddChar (-k) = 1 := by
    have := congrArg (fun f => f 1) h
    simpa [cyclic_matrix_fourier_compl_adjMatrix_char] using this
  rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))] at h1
  have : (-k : ZMod N) = 0 := ZMod.injective_stdAddChar h1
  simp at this
  exact hk this

private lemma cyclic_matrix_fourier_compl_adjMatrix_char_sum (N : ℕ) [NeZero N] (k : ZMod N) :
    ∑ x : ZMod N, cyclic_matrix_fourier_compl_adjMatrix_char N k x =
      if k = 0 then (N : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk; simp [cyclic_matrix_fourier_compl_adjMatrix_char, ZMod.card]
  · rw [if_neg hk,
      AddChar.sum_eq_zero_of_ne_one (cyclic_matrix_fourier_compl_adjMatrix_char_ne_one N k hk)]

private lemma cyclic_matrix_fourier_compl_adjMatrix_exp_eq_char_mul (N : ℕ) [NeZero N]
    (a b x y : ZMod N) :
    Complex.exp (-2 * Real.pi * Complex.I * (((a * x + b * y).val : ℂ) / (N : ℂ)))
      = cyclic_matrix_fourier_compl_adjMatrix_char N a x *
        cyclic_matrix_fourier_compl_adjMatrix_char N b y := by
  rw [cyclic_matrix_fourier_compl_adjMatrix_exp_eq_stdAddChar_neg,
    cyclic_matrix_fourier_compl_adjMatrix_char_mem,
    cyclic_matrix_fourier_compl_adjMatrix_char_mem, ← AddChar.map_add_eq_mul]
  congr 1
  rw [neg_add]

private lemma cyclic_matrix_fourier_compl_adjMatrix_exp_eq_char_two (N : ℕ) [NeZero N]
    (a b x : ZMod N) :
    Complex.exp (-2 * Real.pi * Complex.I * (((a * x + b * x).val : ℂ) / (N : ℂ)))
      = cyclic_matrix_fourier_compl_adjMatrix_char N (a + b) x := by
  rw [cyclic_matrix_fourier_compl_adjMatrix_exp_eq_char_mul,
    cyclic_matrix_fourier_compl_adjMatrix_char_mem,
    cyclic_matrix_fourier_compl_adjMatrix_char_mem,
    cyclic_matrix_fourier_compl_adjMatrix_char_mem, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← neg_add, add_mul]

private lemma cyclic_matrix_fourier_compl_adjMatrix_sum_const (N : ℕ) [NeZero N] (m n : ZMod N) :
    ∑ x : ZMod N, ∑ y : ZMod N,
      Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
      = (if m = 0 then (N : ℂ) else 0) * (if n = 0 then (N : ℂ) else 0) := by
  simp only [cyclic_matrix_fourier_compl_adjMatrix_exp_eq_char_mul]
  rw [← Finset.sum_mul_sum]
  rw [cyclic_matrix_fourier_compl_adjMatrix_char_sum,
    cyclic_matrix_fourier_compl_adjMatrix_char_sum]

private lemma cyclic_matrix_fourier_compl_adjMatrix_sum_ident (N : ℕ) [NeZero N] (m n : ZMod N) :
    ∑ x : ZMod N, ∑ y : ZMod N,
      (if x = y then (1:ℂ) else 0) *
      Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
      = if m + n = 0 then (N : ℂ) else 0 := by
  have h : ∀ x : ZMod N, ∑ y : ZMod N,
      (if x = y then (1:ℂ) else 0) *
      Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
      = cyclic_matrix_fourier_compl_adjMatrix_char N (m + n) x := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl, one_mul, cyclic_matrix_fourier_compl_adjMatrix_exp_eq_char_two]
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  simp only [h]
  rw [cyclic_matrix_fourier_compl_adjMatrix_char_sum]

private lemma cyclic_matrix_fourier_compl_adjMatrix_compl_apply (N : ℕ)
    (G : SimpleGraph (ZMod N)) [DecidableRel G.Adj] (x y : ZMod N) :
    SimpleGraph.adjMatrix ℂ Gᶜ x y =
      1 - (if x = y then (1:ℂ) else 0) - SimpleGraph.adjMatrix ℂ G x y := by
  by_cases hxy : x = y
  · subst hxy
    simp [SimpleGraph.adjMatrix, SimpleGraph.compl_adj]
  · by_cases h : G.Adj x y
    · simp [SimpleGraph.adjMatrix, SimpleGraph.compl_adj, hxy, h]
    · simp [SimpleGraph.adjMatrix, SimpleGraph.compl_adj, hxy, h]

private lemma cyclic_matrix_fourier_compl_adjMatrix_one_div_mul_ite (N : ℕ) [NeZero N]
    (P : Prop) [Decidable P] :
    (1 / (N:ℂ)) * (if P then (N:ℂ) else 0) = if P then 1 else 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases hP : P
  · simp only [hP, if_true]
    field_simp
  · simp [hP]

private lemma cyclic_matrix_fourier_compl_adjMatrix_one_div_mul_ite_mul_ite (N : ℕ) [NeZero N]
    (P Q : Prop) [Decidable P] [Decidable Q] :
    (1 / (N:ℂ)) * ((if P then (N:ℂ) else 0) * (if Q then (N:ℂ) else 0))
      = if P ∧ Q then (N:ℂ) else 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  · field_simp

/-- The 2D cyclic Fourier transform of the complement graph's adjacency matrix. -/
theorem cyclic_matrix_fourier_compl_adjMatrix (N : ℕ) [NeZero N]
    (G : SimpleGraph (ZMod N)) [DecidableRel G.Adj] (m n : ZMod N) :
    cyclic_matrix_fourier N (Gᶜ.adjMatrix ℂ) m n =
      (if m = 0 ∧ n = 0 then (N : ℂ) else 0) -
      (if m + n = 0 then 1 else 0) -
      cyclic_matrix_fourier N (G.adjMatrix ℂ) m n := by
  simp only [cyclic_matrix_fourier, Matrix.of_apply]
  have key : ∀ x y : ZMod N,
      SimpleGraph.adjMatrix ℂ Gᶜ x y *
        Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
      = Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
        - (if x = y then (1:ℂ) else 0) *
          Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ)))
        - SimpleGraph.adjMatrix ℂ G x y *
          Complex.exp (-2 * Real.pi * Complex.I * (((m * x + n * y).val : ℂ) / (N : ℂ))) := by
    intro x y
    rw [cyclic_matrix_fourier_compl_adjMatrix_compl_apply]
    ring
  simp only [key, Finset.sum_sub_distrib]
  rw [cyclic_matrix_fourier_compl_adjMatrix_sum_const,
    cyclic_matrix_fourier_compl_adjMatrix_sum_ident]
  rw [mul_sub, mul_sub,
    cyclic_matrix_fourier_compl_adjMatrix_one_div_mul_ite_mul_ite,
    cyclic_matrix_fourier_compl_adjMatrix_one_div_mul_ite]
