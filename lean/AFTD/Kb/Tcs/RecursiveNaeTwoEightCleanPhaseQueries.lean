import AFTD.Prelude
import AFTD.Kb.Tcs.PhaseQueryComputesCleanly
import AFTD.Kb.Tcs.RecursiveNae

/-!
# recursive_nae_two_eight_clean_phase_queries

Topic: quantum   Node: 6f4c6fd40e9b

Provenance: formalization of a published result. Source: arXiv:1211.0721 Section 3.4, Construction 1: an eight-query (-1)-computation of the depth-two function, expressed in the present phase-query circuit model.

There exists an eight-query clean phase circuit for recursive ternary not-all-equal at depth two.
-/

def rnae8_blk (a : Fin 13) : ℕ := a.val / 3

def rnae8_kd (a b : Fin 13) : ℤ := if a = b then 1 else 0

def rnae8_Dz : Matrix (Fin 13) (Fin 13) ℤ := Matrix.of fun a b =>
  if a.val < 9 ∧ b.val < 9 then (if rnae8_blk a = rnae8_blk b then 2 else 0) - 3 * rnae8_kd a b else 3 * rnae8_kd a b

def rnae8_T2z : Matrix (Fin 13) (Fin 13) ℤ := Matrix.of fun a b =>
  if a.val < 9 ∧ b.val < 9 then 9 * rnae8_kd a b - (if rnae8_blk a = rnae8_blk b then 6 else 0) + 2 else 9 * rnae8_kd a b

def rnae8_nz (a : Fin 13) : ℤ :=
  if a.val < 9 then 9 else if a.val = 9 then 17 else if a.val = 10 then 2 else 1

def rnae8_Rz : Matrix (Fin 13) (Fin 13) ℤ := Matrix.of fun a b => rnae8_nz a * rnae8_nz b - 512 * rnae8_kd a b

def rnae8_Iz : Matrix (Fin 13) (Fin 13) ℤ := Matrix.of rnae8_kd

def rnae8_stepsZ : Fin 8 → ℕ × Matrix (Fin 13) (Fin 13) ℤ :=
  ![(3, rnae8_Dz), (9, rnae8_T2z), (3, rnae8_Dz), (512, rnae8_Rz), (3, rnae8_Dz), (9, rnae8_T2z), (3, rnae8_Dz), (1, rnae8_Iz)]

def rnae8_reg (b : Fin 13) : Option (Fin (3 ^ 2)) := if h : b.val < 9 then some ⟨b.val, h⟩ else none

def rnae8_phz (x : Fin (3 ^ 2) → Bool) (b : Fin 13) : ℤ :=
  match rnae8_reg b with | none => 1 | some i => if x i then -1 else 1

def rnae8_stepZ (ph : Fin 13 → ℤ) (w : Fin 13 → ℤ) (p : ℕ × Matrix (Fin 13) (Fin 13) ℤ) : Fin 13 → ℤ :=
  p.2.mulVec (fun b => ph b * w b)

def rnae8_evalZ (x : Fin (3 ^ 2) → Bool) : Fin 13 → ℤ :=
  (List.ofFn rnae8_stepsZ).foldl (rnae8_stepZ (rnae8_phz x)) rnae8_nz

def rnae8_bsum (w : Fin 13 → ℤ) (k : ℕ) : ℤ :=
  match k with
  | 0 => w 0 + w 1 + w 2
  | 1 => w 3 + w 4 + w 5
  | _ => w 6 + w 7 + w 8

def rnae8_tot (w : Fin 13 → ℤ) : ℤ := rnae8_bsum w 0 + rnae8_bsum w 1 + rnae8_bsum w 2

def rnae8_fastD (w : Fin 13 → ℤ) (i : Fin 13) : ℤ :=
  if i.val < 9 then 2 * rnae8_bsum w (i.val / 3) - 3 * w i else 3 * w i

def rnae8_fastT (w : Fin 13 → ℤ) (i : Fin 13) : ℤ :=
  if i.val < 9 then 9 * w i - 6 * rnae8_bsum w (i.val / 3) + 2 * rnae8_tot w else 9 * w i

def rnae8_dotn (w : Fin 13 → ℤ) : ℤ := 9 * rnae8_tot w + 17 * w 9 + 2 * w 10 + w 11 + w 12

def rnae8_fastR (w : Fin 13 → ℤ) (i : Fin 13) : ℤ := rnae8_nz i * rnae8_dotn w - 512 * w i

theorem rnae8_Dz_fast (w : Fin 13 → ℤ) : rnae8_Dz.mulVec w = rnae8_fastD w := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, rnae8_Dz, rnae8_kd, rnae8_blk, rnae8_fastD, rnae8_bsum] <;> ring

theorem rnae8_T2z_fast (w : Fin 13 → ℤ) : rnae8_T2z.mulVec w = rnae8_fastT w := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, rnae8_T2z, rnae8_kd, rnae8_blk, rnae8_fastT, rnae8_bsum, rnae8_tot] <;> ring

theorem rnae8_Rz_fast (w : Fin 13 → ℤ) : rnae8_Rz.mulVec w = rnae8_fastR w := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, rnae8_Rz, rnae8_kd, rnae8_nz, rnae8_fastR, rnae8_dotn, rnae8_bsum, rnae8_tot] <;> ring

theorem rnae8_Iz_fast (w : Fin 13 → ℤ) : rnae8_Iz.mulVec w = w := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, rnae8_Iz, rnae8_kd]

def rnae8_evalF (x : Fin (3 ^ 2) → Bool) : Fin 13 → ℤ :=
  let q := fun (w : Fin 13 → ℤ) (b : Fin 13) => rnae8_phz x b * w b
  let v1 := rnae8_fastD (q rnae8_nz)
  let v2 := rnae8_fastT (q v1)
  let v3 := rnae8_fastD (q v2)
  let v4 := rnae8_fastR (q v3)
  let v5 := rnae8_fastD (q v4)
  let v6 := rnae8_fastT (q v5)
  let v7 := rnae8_fastD (q v6)
  q v7

theorem rnae8_evalZ_eq (x : Fin (3 ^ 2) → Bool) : rnae8_evalZ x = rnae8_evalF x := by
  simp only [rnae8_evalZ, rnae8_evalF, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, rnae8_stepZ, rnae8_stepsZ]
  simp [rnae8_Dz_fast, rnae8_T2z_fast, rnae8_Rz_fast, rnae8_Iz_fast]

set_option maxRecDepth 100000 in
theorem rnae8_allbF : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, ∀ b,
    rnae8_evalF (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin (3 ^ 2) → Bool) b
    = (if recursive_nae 2 (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin (3 ^ 2) → Bool) then -1 else 1)
      * 3359232 * rnae8_nz b := by
  decide +kernel

theorem rnae8_allx : ∀ x : Fin (3 ^ 2) → Bool, ∀ b, rnae8_evalZ x b
    = (if recursive_nae 2 x then -1 else 1) * 3359232 * rnae8_nz b := by
  intro x
  have hx : x = (![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] : Fin (3 ^ 2) → Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hx]
  rw [rnae8_evalZ_eq]
  exact rnae8_allbF _ _ _ _ _ _ _ _ _

set_option maxRecDepth 100000 in
theorem rnae8_unitZ : ∀ t, Matrix.transpose (rnae8_stepsZ t).2 * (rnae8_stepsZ t).2 = ((rnae8_stepsZ t).1 ^ 2 : ℤ) • (1 : Matrix (Fin 13) (Fin 13) ℤ) := by
  decide +kernel

theorem rnae8_normZ : ∑ b, rnae8_nz b * rnae8_nz b = 1024 := by decide +kernel

theorem rnae8_prodZ : ((List.ofFn rnae8_stepsZ).map (fun p => (p.1 : ℂ))).prod = 3359232 := by
  simp [List.ofFn_succ, rnae8_stepsZ]
  norm_num

noncomputable def rnae8_toC (p : ℕ × Matrix (Fin 13) (Fin 13) ℤ) : Matrix (Fin 13) (Fin 13) ℂ :=
  ((p.1 : ℂ)⁻¹) • p.2.map (Int.castRingHom ℂ)

theorem rnae8_step_cast (ph : Fin 13 → ℤ) {phC : Fin 13 → ℂ} (hC : ∀ b, phC b = ((ph b : ℤ) : ℂ))
    (p : ℕ × Matrix (Fin 13) (Fin 13) ℤ) (c : ℂ) (v : Fin 13 → ℤ) :
    (rnae8_toC p).mulVec (fun b => phC b * (c * ((v b : ℤ) : ℂ)))
      = fun b => (c * (p.1 : ℂ)⁻¹) * ((rnae8_stepZ ph v p b : ℤ) : ℂ) := by
  funext i
  simp only [rnae8_toC, rnae8_stepZ, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply,
    Int.coe_castRingHom, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hC]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rnae8_foldl_cast (ph : Fin 13 → ℤ) {phC : Fin 13 → ℂ} (hC : ∀ b, phC b = ((ph b : ℤ) : ℂ)) :
    ∀ (L : List (ℕ × Matrix (Fin 13) (Fin 13) ℤ)) (c : ℂ) (v : Fin 13 → ℤ),
    (L.map rnae8_toC).foldl (fun w U => U.mulVec (fun b => phC b * w b)) (fun b => c * ((v b : ℤ) : ℂ))
      = fun b => (c / (L.map (fun p => (p.1 : ℂ))).prod) * (((L.foldl (rnae8_stepZ ph) v) b : ℤ) : ℂ)
  | [], c, v => by simp
  | p :: L, c, v => by
    simp only [List.map_cons, List.foldl_cons, List.prod_cons]
    rw [rnae8_step_cast ph hC, rnae8_foldl_cast ph hC L]
    funext b
    rw [div_mul_eq_div_div, div_eq_mul_inv c (p.1 : ℂ)]

/-- The known eight-query clean phase circuit at depth two. -/
theorem recursive_nae_two_eight_clean_phase_queries : phase_query_computes_cleanly (recursive_nae 2) 8 := by
  refine ⟨Fin 13, inferInstance, inferInstance, rnae8_reg, fun b => (32 : ℂ)⁻¹ * ((rnae8_nz b : ℤ) : ℂ), ?_, 1,
    Submonoid.one_mem _, fun t => rnae8_toC (rnae8_stepsZ t), ?_, ?_⟩
  · have h1 : ∀ b, Complex.normSq ((32 : ℂ)⁻¹ * ((rnae8_nz b : ℤ) : ℂ)) = ((rnae8_nz b * rnae8_nz b : ℤ) : ℝ) / 1024 := by
      intro b
      rw [Complex.normSq_mul]
      have : ((rnae8_nz b : ℤ) : ℂ) = (((rnae8_nz b : ℤ) : ℝ) : ℂ) := by simp
      rw [this, Complex.normSq_ofReal]
      simp [Complex.normSq_apply]
      ring
    simp only [h1]
    rw [← Finset.sum_div, ← Int.cast_sum, rnae8_normZ]
    norm_num
  · intro t
    rw [Matrix.mem_unitaryGroup_iff']
    have hd : ((rnae8_stepsZ t).1 : ℂ) ≠ 0 := by
      fin_cases t <;> simp [rnae8_stepsZ]
    have hs : star (rnae8_toC (rnae8_stepsZ t)) = ((rnae8_stepsZ t).1 : ℂ)⁻¹ • (Matrix.transpose (rnae8_stepsZ t).2).map (Int.castRingHom ℂ) := by
      ext i j
      simp [rnae8_toC, Matrix.star_apply]
    show star (rnae8_toC (rnae8_stepsZ t)) * rnae8_toC (rnae8_stepsZ t) = 1
    rw [hs]
    unfold rnae8_toC
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, rnae8_unitZ t]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hd]
    field_simp
  · intro x b
    rw [Matrix.one_mulVec,
      show (List.ofFn fun t => rnae8_toC (rnae8_stepsZ t)) = (List.ofFn rnae8_stepsZ).map rnae8_toC by rw [List.map_ofFn]; rfl,
      rnae8_foldl_cast (rnae8_phz x) ?hC (List.ofFn rnae8_stepsZ) _ rnae8_nz, rnae8_prodZ]
    · show _ * ((rnae8_evalZ x b : ℤ) : ℂ) = _
      rw [rnae8_allx x b]
      by_cases hf : recursive_nae 2 x <;> simp [hf] <;> ring
    · intro c
      unfold rnae8_phz
      cases rnae8_reg c with
      | none => simp
      | some i => by_cases hx : x i <;> simp [hx]
