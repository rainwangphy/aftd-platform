import AFTD.Prelude
import AFTD.Kb.Physics.InstFintypeCondPhyslib
import AFTD.Kb.Physics.EquivFinAddEquivSigmaCond
import AFTD.Kb.Physics.InstDecidableEqSigmaBoolCondPhyslib
import AFTD.Kb.Physics.EquivFinAddEquivSigmaCondTrue
import AFTD.Kb.Physics.FinSubNat'
import AFTD.Kb.Physics.EquivFinAddEquivSigmaCondFalse
import AFTD.Kb.Physics.LinearMapSchurTriangulationAux

/-!
# LinearMap.SchurTriangulationAux.of

Topic: classical_mechanics   Node: bf0021d7ac95

Provenance: formalization of a published result. Source: Physlib, `LinearMap.SchurTriangulationAux.of`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 adapted; compiled here.

**Don't use this definition directly.** This is the key algorithm behind `Matrix.schur_triangulation`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearMap in
open scoped InnerProductSpace in
open Module in
variable [RCLike 𝕜] in
variable [IsAlgClosed 𝕜] in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
/-- **Don't use this definition directly.** This is the key algorithm behind `Matrix.schur_triangulation`. -/
protected noncomputable def LinearMap.SchurTriangulationAux.of
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : Module.End 𝕜 E) :
    SchurTriangulationAux f :=
  haveI : Decidable (Nontrivial E) := Classical.propDecidable _
  if hE : Nontrivial E then
    let μ : f.Eigenvalues := default
    let V : Submodule 𝕜 E := f.eigenspace μ
    let W : Submodule 𝕜 E := Vᗮ
    let m := Module.finrank 𝕜 V
    have hdim : m + Module.finrank 𝕜 W = Module.finrank 𝕜 E := V.finrank_add_finrank_orthogonal
    let g : Module.End 𝕜 W := Submodule.orthogonalProjectionOnto W ∘ₗ f.domRestrict W
    let ⟨n, hn, bW, hg⟩ := SchurTriangulationAux.of g

    have bV : OrthonormalBasis (Fin m) 𝕜 V := stdOrthonormalBasis 𝕜 V
    have hV := V.orthogonalFamily_self
    have int : DirectSum.IsInternal (cond · V W) :=
      suffices ⨆ b, cond b V W = ⊤ from (hV.decomposition this).isInternal _
      (sup_eq_iSup V W).symm.trans Submodule.sup_orthogonal_of_hasOrthogonalProjection
    let B (b : Bool) : OrthonormalBasis (cond b (Fin m) (Fin n)) 𝕜 ↥(cond b V W) := b.rec bW bV
    let bE : OrthonormalBasis (Σ b, cond b (Fin m) (Fin n)) 𝕜 E :=
      int.collectedOrthonormalBasis hV B
    let e := Equiv.finAddEquivSigmaCond
    let basis := bE.reindex e.symm
    {
      basis
      dim := m + n
      hdim := hn ▸ hdim.symm
      upperTriangular := fun i j (hji : j < i) => show toMatrixOrthonormal basis f i j = 0 from
        have hB : ∀ s, bE s = B s.1 s.2
          | ⟨true, i⟩ => show bE ⟨true, i⟩ = bV i from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨true, i⟩ = bV i
            by simp only [Basis.coe_toOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe,
              Bool.cond_true, OrthonormalBasis.coe_toBasis, B, V, W]
          | ⟨false, j⟩ => show bE ⟨false, j⟩ = bW j from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨false, j⟩ = bW j
            by simp only [Basis.coe_toOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe,
              Bool.cond_false, OrthonormalBasis.coe_toBasis, B, V, W]
        have hf {bi i' bj j'} (hi : e i = ⟨bi, i'⟩) (hj : e j = ⟨bj, j'⟩) :=
          calc toMatrixOrthonormal basis f i j
            _ = toMatrixOrthonormal bE f (e i) (e j) := by
              rw [f.toMatrixOrthonormal_reindex]
              rfl
            _ = ⟪bE (e i), f (bE (e j))⟫_𝕜 := f.toMatrixOrthonormal_apply_apply ..
            _ = ⟪(B bi i' : E), f (B bj j')⟫_𝕜 := by rw [hB, hB, hi, hj]

        if hj : j < m then
          let j' : Fin m := ⟨j, hj⟩
          have hf' {bi i'} (hi : e i = ⟨bi, i'⟩) (h0 : ⟪(B bi i' : E), bV j'⟫_𝕜 = 0) :=
            calc toMatrixOrthonormal basis f i j
              _ = ⟪(B bi i' : E), f _⟫_𝕜 := hf hi (Equiv.finAddEquivSigmaCond_true hj)
              _ = ⟪_, f (bV j')⟫_𝕜 := rfl
              _ = 0 :=
                suffices f (bV j') = μ.val • bV j' by rw [this, inner_smul_right, h0, mul_zero]
                suffices f.HasEigenvector μ (bV j') from this.apply_eq_smul
                ⟨(bV j').property, fun h => bV.toBasis.ne_zero j' (Subtype.ext h)⟩

          if hi : i < m then
            let i' : Fin m := ⟨i, hi⟩
            suffices ⟪(bV i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_true hi) this
            bV.orthonormal.right (Fin.ne_of_gt hji)
          else
            let i' : Fin n := i.subNat' hi
            suffices ⟪(bW i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_false hi) this
            V.inner_left_of_mem_orthogonal (bV j').property (bW i').property
        else
          have hi (h : i < m) : False := hj (Nat.lt_trans hji h)
          let i' : Fin n := i.subNat' hi
          let j' : Fin n := j.subNat' hj
          calc toMatrixOrthonormal basis f i j
            _ = ⟪(bW i' : E), f (bW j')⟫_𝕜 :=
              hf (Equiv.finAddEquivSigmaCond_false hi) (Equiv.finAddEquivSigmaCond_false hj)
            _ = ⟪bW i', g (bW j')⟫_𝕜 := by
              rw [coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, domRestrict_apply,
                Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
            _ = toMatrixOrthonormal bW g i' j' := (g.toMatrixOrthonormal_apply_apply ..).symm
            _ = 0 := hg (Nat.sub_lt_sub_right (Nat.le_of_not_lt hj) hji)
    }
  else
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    {
      dim := 0
      hdim := Module.finrank_zero_of_subsingleton
      basis := (Basis.empty E).toOrthonormalBasis ⟨nofun, nofun⟩
      upperTriangular := nofun
    }
termination_by Module.finrank 𝕜 E
decreasing_by exact
  calc Module.finrank 𝕜 W
    _ < m + Module.finrank 𝕜 W :=
      suffices 0 < m from Nat.lt_add_of_pos_left this
      Submodule.one_le_finrank_iff.mpr μ.property
    _ = Module.finrank 𝕜 E := hdim
