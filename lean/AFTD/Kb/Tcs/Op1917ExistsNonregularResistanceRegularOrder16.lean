import AFTD.Prelude
import AFTD.Kb.Tcs.IsResistanceRegular
import AFTD.Kb.Tcs.F4AdjBool
import AFTD.Kb.Tcs.F4Graph
import AFTD.Kb.Tcs.IsMoorePenroseInverse
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.F

/-!
# op1917_exists_nonregular_resistance_regular_order_16

Topic: graphs   Node: f45b131ad725

Provenance: formalization of a published result. Source: arXiv:2611.21670 Theorem B

There exists a finite type V with 16 elements and a simple graph G on V such that G is resistance-regular and G is not regular (there does not exist d such that G is regular of degree d).
-/

open SimpleGraph Matrix

/-- Neighbour lists of the vertex i of the 16-vertex witness graph F(4). -/
def op1917_exists_nonregular_resistance_regular_order_16_nbrs : Nat → List Nat
  | 0 => [1,2,3,8,9,10,11]
  | 1 => [0,2,3,8,9,10,11]
  | 2 => [0,1,3,8,9,10,11]
  | 3 => [0,1,2,8,9,10,11]
  | 4 => [5,6,7,12,13,14,15]
  | 5 => [4,6,7,12,13,14,15]
  | 6 => [4,5,7,12,13,14,15]
  | 7 => [4,5,6,12,13,14,15]
  | 8 => [0,1,2,3,9,13]
  | 9 => [0,1,2,3,8,12]
  | 10 => [0,1,2,3,11,15]
  | 11 => [0,1,2,3,10,14]
  | 12 => [4,5,6,7,9,13]
  | 13 => [4,5,6,7,8,12]
  | 14 => [4,5,6,7,11,15]
  | 15 => [4,5,6,7,10,14]
  | _ => []

/-- Boolean adjacency relation of the witness graph. -/
def op1917_exists_nonregular_resistance_regular_order_16_adjb (v w : Fin 16) : Bool :=
  (op1917_exists_nonregular_resistance_regular_order_16_nbrs v.val).contains w.val

/-- The witness adjacency is symmetric. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_adjb_symm :
    ∀ a b : Fin 16, op1917_exists_nonregular_resistance_regular_order_16_adjb a b =
      op1917_exists_nonregular_resistance_regular_order_16_adjb b a := by
  intro a b; fin_cases a <;> fin_cases b <;> decide

/-- The witness adjacency is loopless. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_adjb_irrefl :
    ∀ a : Fin 16, op1917_exists_nonregular_resistance_regular_order_16_adjb a a = false := by
  intro a; fin_cases a <;> decide

/-- The 16-vertex witness graph F(4) of arXiv:2611.21670. -/
def op1917_exists_nonregular_resistance_regular_order_16_graph : SimpleGraph (Fin 16) where
  Adj v w := op1917_exists_nonregular_resistance_regular_order_16_adjb v w = true
  symm := ⟨fun a b h => by
    rw [← op1917_exists_nonregular_resistance_regular_order_16_adjb_symm a b]; exact h⟩
  loopless := ⟨fun a h => by
    simp [op1917_exists_nonregular_resistance_regular_order_16_adjb_irrefl a] at h⟩

instance op1917_exists_nonregular_resistance_regular_order_16_graph_decRel :
    DecidableRel op1917_exists_nonregular_resistance_regular_order_16_graph.Adj :=
  fun v w => inferInstanceAs
    (Decidable (op1917_exists_nonregular_resistance_regular_order_16_adjb v w = true))

/-- An explicit edge of the witness graph yields reachability. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_edge (u v : Fin 16)
    (h : op1917_exists_nonregular_resistance_regular_order_16_adjb u v = true) :
    op1917_exists_nonregular_resistance_regular_order_16_graph.Reachable u v :=
  SimpleGraph.Adj.reachable h

/-- Vertex 0 reaches every vertex of the witness graph through a short explicit walk. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_reach (v : Fin 16) :
    op1917_exists_nonregular_resistance_regular_order_16_graph.Reachable 0 v := by
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 1 (by decide)
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 2 (by decide)
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 3 (by decide)
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)).trans
      ((op1917_exists_nonregular_resistance_regular_order_16_edge 8 13 (by decide)).trans
        (op1917_exists_nonregular_resistance_regular_order_16_edge 13 4 (by decide)))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)).trans
      ((op1917_exists_nonregular_resistance_regular_order_16_edge 8 13 (by decide)).trans
        ((op1917_exists_nonregular_resistance_regular_order_16_edge 13 4 (by decide)).trans
          (op1917_exists_nonregular_resistance_regular_order_16_edge 4 5 (by decide))))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)).trans
      ((op1917_exists_nonregular_resistance_regular_order_16_edge 8 13 (by decide)).trans
        ((op1917_exists_nonregular_resistance_regular_order_16_edge 13 4 (by decide)).trans
          (op1917_exists_nonregular_resistance_regular_order_16_edge 4 6 (by decide))))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)).trans
      ((op1917_exists_nonregular_resistance_regular_order_16_edge 8 13 (by decide)).trans
        ((op1917_exists_nonregular_resistance_regular_order_16_edge 13 4 (by decide)).trans
          (op1917_exists_nonregular_resistance_regular_order_16_edge 4 7 (by decide))))
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 9 (by decide)
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 10 (by decide)
  · exact op1917_exists_nonregular_resistance_regular_order_16_edge 0 11 (by decide)
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 9 (by decide)).trans
      (op1917_exists_nonregular_resistance_regular_order_16_edge 9 12 (by decide))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 8 (by decide)).trans
      (op1917_exists_nonregular_resistance_regular_order_16_edge 8 13 (by decide))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 11 (by decide)).trans
      (op1917_exists_nonregular_resistance_regular_order_16_edge 11 14 (by decide))
  · exact (op1917_exists_nonregular_resistance_regular_order_16_edge 0 10 (by decide)).trans
      (op1917_exists_nonregular_resistance_regular_order_16_edge 10 15 (by decide))

/-- The witness graph is connected. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_connected :
    op1917_exists_nonregular_resistance_regular_order_16_graph.Connected := by
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact (op1917_exists_nonregular_resistance_regular_order_16_reach u).symm.trans
    (op1917_exists_nonregular_resistance_regular_order_16_reach v)

/-- The integer Laplacian matrix of the witness graph. -/
def op1917_exists_nonregular_resistance_regular_order_16_L : Matrix (Fin 16) (Fin 16) ℤ :=
  op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℤ

/-- 384 times the Moore–Penrose pseudoinverse of the witness Laplacian (an integer matrix). -/
def op1917_exists_nonregular_resistance_regular_order_16_M : Matrix (Fin 16) (Fin 16) ℤ :=
 !![75, 27, 27, 27, -33, -33, -33, -33, 21, 21, 21, 21, -27, -27, -27, -27;
    27, 75, 27, 27, -33, -33, -33, -33, 21, 21, 21, 21, -27, -27, -27, -27;
    27, 27, 75, 27, -33, -33, -33, -33, 21, 21, 21, 21, -27, -27, -27, -27;
    27, 27, 27, 75, -33, -33, -33, -33, 21, 21, 21, 21, -27, -27, -27, -27;
    -33, -33, -33, -33, 75, 27, 27, 27, -27, -27, -27, -27, 21, 21, 21, 21;
    -33, -33, -33, -33, 27, 75, 27, 27, -27, -27, -27, -27, 21, 21, 21, 21;
    -33, -33, -33, -33, 27, 27, 75, 27, -27, -27, -27, -27, 21, 21, 21, 21;
    -33, -33, -33, -33, 27, 27, 27, 75, -27, -27, -27, -27, 21, 21, 21, 21;
    21, 21, 21, 21, -27, -27, -27, -27, 75, 19, 7, 7, -21, -13, -25, -25;
    21, 21, 21, 21, -27, -27, -27, -27, 19, 75, 7, 7, -13, -21, -25, -25;
    21, 21, 21, 21, -27, -27, -27, -27, 7, 7, 75, 19, -25, -25, -21, -13;
    21, 21, 21, 21, -27, -27, -27, -27, 7, 7, 19, 75, -25, -25, -13, -21;
    -27, -27, -27, -27, 21, 21, 21, 21, -21, -13, -25, -25, 75, 19, 7, 7;
    -27, -27, -27, -27, 21, 21, 21, 21, -13, -21, -25, -25, 19, 75, 7, 7;
    -27, -27, -27, -27, 21, 21, 21, 21, -25, -25, -21, -13, 7, 7, 75, 19;
    -27, -27, -27, -27, 21, 21, 21, 21, -25, -25, -13, -21, 7, 7, 19, 75]

/-- The candidate pseudoinverse scaled into the reals. -/
def op1917_exists_nonregular_resistance_regular_order_16_MR : Matrix (Fin 16) (Fin 16) ℝ :=
  op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ)

/-- Entrywise description of the real scaled pseudoinverse. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_MR_apply (i j : Fin 16) :
    op1917_exists_nonregular_resistance_regular_order_16_MR i j =
      ((op1917_exists_nonregular_resistance_regular_order_16_M i j : ℤ) : ℝ) := by
  rw [show op1917_exists_nonregular_resistance_regular_order_16_MR =
      op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ) from rfl,
    Matrix.map_apply, Int.coe_castRingHom]

/-- The integer identity `L M L = 384 L`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_LML_apply (i j : Fin 16) :
    (op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L) i j =
    384 * op1917_exists_nonregular_resistance_regular_order_16_L i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The integer identity `M L M = 384 M`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_MLM_apply (i j : Fin 16) :
    (op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M) i j =
    384 * op1917_exists_nonregular_resistance_regular_order_16_M i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The integer product `L M` is symmetric. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_LM_symm_apply (i j : Fin 16) :
    (op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M) j i =
    (op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M) i j := by
  have h := congrFun (congrFun (show
    (op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M).transpose =
    op1917_exists_nonregular_resistance_regular_order_16_L *
      op1917_exists_nonregular_resistance_regular_order_16_M from by decide) i) j
  simpa [Matrix.transpose_apply] using h

/-- The integer product `M L` is symmetric. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_ML_symm_apply (i j : Fin 16) :
    (op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L) j i =
    (op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L) i j := by
  have h := congrFun (congrFun (show
    (op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L).transpose =
    op1917_exists_nonregular_resistance_regular_order_16_M *
      op1917_exists_nonregular_resistance_regular_order_16_L from by decide) i) j
  simpa [Matrix.transpose_apply] using h

/-- The real Laplacian is the cast of the integer Laplacian. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast :
    op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ =
      op1917_exists_nonregular_resistance_regular_order_16_L.map (Int.castRingHom ℝ) := by
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.sub_apply,
    Matrix.map_apply, Matrix.diagonal_apply, Matrix.of_apply,
    op1917_exists_nonregular_resistance_regular_order_16_L]
  split_ifs with h1 h2 <;> push_cast <;> norm_num

/-- Entrywise form of the cast of the integer Laplacian. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast_apply (i j : Fin 16) :
    op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ i j =
      ((op1917_exists_nonregular_resistance_regular_order_16_L i j : ℤ) : ℝ) := by
  rw [op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast, Matrix.map_apply,
    Int.coe_castRingHom]

/-- Real version of `L M L = 384 L`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_real_LML :
    op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
        op1917_exists_nonregular_resistance_regular_order_16_MR *
        op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ =
      (384 : ℝ) • op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ := by
  have hmap : op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
        op1917_exists_nonregular_resistance_regular_order_16_MR *
        op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ =
      (op1917_exists_nonregular_resistance_regular_order_16_L *
        op1917_exists_nonregular_resistance_regular_order_16_M *
        op1917_exists_nonregular_resistance_regular_order_16_L).map (Int.castRingHom ℝ) := by
    rw [op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast,
      show op1917_exists_nonregular_resistance_regular_order_16_MR =
        op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ) from rfl,
      ← Matrix.map_mul, ← Matrix.map_mul]
  rw [hmap]
  ext i j
  rw [Matrix.map_apply, Int.coe_castRingHom, Matrix.smul_apply, smul_eq_mul,
    op1917_exists_nonregular_resistance_regular_order_16_LML_apply,
    op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast_apply]
  show ((384 * op1917_exists_nonregular_resistance_regular_order_16_L i j : ℤ) : ℝ) =
    384 * ((op1917_exists_nonregular_resistance_regular_order_16_L i j : ℤ) : ℝ)
  rw [Int.cast_mul, Int.cast_ofNat]

/-- Real version of `M L M = 384 M`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_real_MLM :
    op1917_exists_nonregular_resistance_regular_order_16_MR *
        op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
        op1917_exists_nonregular_resistance_regular_order_16_MR =
      (384 : ℝ) • op1917_exists_nonregular_resistance_regular_order_16_MR := by
  have hmap : op1917_exists_nonregular_resistance_regular_order_16_MR *
        op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
        op1917_exists_nonregular_resistance_regular_order_16_MR =
      (op1917_exists_nonregular_resistance_regular_order_16_M *
        op1917_exists_nonregular_resistance_regular_order_16_L *
        op1917_exists_nonregular_resistance_regular_order_16_M).map (Int.castRingHom ℝ) := by
    rw [op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast,
      show op1917_exists_nonregular_resistance_regular_order_16_MR =
        op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ) from rfl,
      ← Matrix.map_mul, ← Matrix.map_mul]
  rw [hmap]
  ext i j
  rw [Matrix.map_apply, Int.coe_castRingHom, Matrix.smul_apply, smul_eq_mul,
    op1917_exists_nonregular_resistance_regular_order_16_MLM_apply,
    op1917_exists_nonregular_resistance_regular_order_16_MR_apply]
  show ((384 * op1917_exists_nonregular_resistance_regular_order_16_M i j : ℤ) : ℝ) =
    384 * ((op1917_exists_nonregular_resistance_regular_order_16_M i j : ℤ) : ℝ)
  rw [Int.cast_mul, Int.cast_ofNat]

/-- Real version of the symmetry of `L M`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_real_LM_symm :
    (op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
      op1917_exists_nonregular_resistance_regular_order_16_MR).transpose =
      op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
        op1917_exists_nonregular_resistance_regular_order_16_MR := by
  have hmap : op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ *
      op1917_exists_nonregular_resistance_regular_order_16_MR =
      (op1917_exists_nonregular_resistance_regular_order_16_L *
        op1917_exists_nonregular_resistance_regular_order_16_M).map (Int.castRingHom ℝ) := by
    rw [op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast,
      show op1917_exists_nonregular_resistance_regular_order_16_MR =
        op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ) from rfl,
      ← Matrix.map_mul]
  rw [hmap]
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.map_apply, Int.coe_castRingHom,
    op1917_exists_nonregular_resistance_regular_order_16_LM_symm_apply]

/-- Real version of the symmetry of `M L`. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_real_ML_symm :
    (op1917_exists_nonregular_resistance_regular_order_16_MR *
      op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ).transpose =
      op1917_exists_nonregular_resistance_regular_order_16_MR *
        op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ := by
  have hmap : op1917_exists_nonregular_resistance_regular_order_16_MR *
      op1917_exists_nonregular_resistance_regular_order_16_graph.lapMatrix ℝ =
      (op1917_exists_nonregular_resistance_regular_order_16_M *
        op1917_exists_nonregular_resistance_regular_order_16_L).map (Int.castRingHom ℝ) := by
    rw [op1917_exists_nonregular_resistance_regular_order_16_lapMatrix_cast,
      show op1917_exists_nonregular_resistance_regular_order_16_MR =
        op1917_exists_nonregular_resistance_regular_order_16_M.map (Int.castRingHom ℝ) from rfl,
      ← Matrix.map_mul]
  rw [hmap]
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.map_apply, Int.coe_castRingHom,
    op1917_exists_nonregular_resistance_regular_order_16_ML_symm_apply]

/-- Every diagonal entry of the scaled pseudoinverse is 75. -/
theorem op1917_exists_nonregular_resistance_regular_order_16_MR_diag (v : Fin 16) :
    op1917_exists_nonregular_resistance_regular_order_16_MR v v = 75 := by
  rw [op1917_exists_nonregular_resistance_regular_order_16_MR_apply]
  have h : op1917_exists_nonregular_resistance_regular_order_16_M v v = 75 := by
    fin_cases v <;> decide
  rw [h]
  norm_num

/-- There exists a non-regular resistance-regular graph on 16 vertices (Theorem B, F(4)). -/
theorem op1917_exists_nonregular_resistance_regular_order_16 :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = 16 ∧ is_resistance_regular G ∧ ¬ ∃ d, G.IsRegularOfDegree d := by
  refine ⟨Fin 16, inferInstance, inferInstance,
    op1917_exists_nonregular_resistance_regular_order_16_graph,
    op1917_exists_nonregular_resistance_regular_order_16_graph_decRel, ?_, ?_, ?_⟩
  · simp
  · refine ⟨op1917_exists_nonregular_resistance_regular_order_16_connected,
      (384 : ℝ)⁻¹ • op1917_exists_nonregular_resistance_regular_order_16_MR, ?_, 25 / 128, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Matrix.mul_smul, Matrix.smul_mul,
          op1917_exists_nonregular_resistance_regular_order_16_real_LML, smul_smul,
          show (384 : ℝ)⁻¹ * 384 = 1 by norm_num, one_smul]
      · rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
          op1917_exists_nonregular_resistance_regular_order_16_real_MLM, smul_smul, smul_smul,
          show (384 : ℝ)⁻¹ * (384 : ℝ)⁻¹ * 384 = (384 : ℝ)⁻¹ by norm_num]
      · rw [Matrix.mul_smul, Matrix.transpose_smul,
          op1917_exists_nonregular_resistance_regular_order_16_real_LM_symm]
      · rw [Matrix.smul_mul, Matrix.transpose_smul,
          op1917_exists_nonregular_resistance_regular_order_16_real_ML_symm]
    · intro v
      rw [Matrix.smul_apply, smul_eq_mul,
        op1917_exists_nonregular_resistance_regular_order_16_MR_diag]
      norm_num
  · rintro ⟨d, hd⟩
    have h0 : op1917_exists_nonregular_resistance_regular_order_16_graph.degree (0 : Fin 16) = 7 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]; decide
    have h8 : op1917_exists_nonregular_resistance_regular_order_16_graph.degree (8 : Fin 16) = 6 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]; decide
    have e0 := hd 0
    have e8 := hd 8
    omega
