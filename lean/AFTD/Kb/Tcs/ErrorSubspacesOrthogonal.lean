import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.IsNondegenerate
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.CodeProj
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.CodeProjEqSelfOfMem
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.PauliOpAdjoint
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule
import AFTD.Kb.Tcs.KnillLaflamme

/-!
# error_subspaces_orthogonal

Topic: quantum   Node: ddf7d8ce4dbd

Provenance: helper lemma. TCSlib, `error_subspaces_orthogonal`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 adapted; compiled here.

Orthogonality of distinct error subspaces. Let $C \le \mathcal{H}_n$ be a code that is non-degenerate for $t$-error correction, and
let $E, F$ be Pauli strings on $n$ qubits with weights $\mathrm{wt}(E) \le t$ and
$\mathrm{wt}(F) \le t$ and $E \neq F$. Then the images $\hat{E}(C)$ and $\hat{F}(C)$ of
$C$ under the corresponding Pauli operators are orthogonal subspaces of $\mathcal{H}_n$;
that is, $\langle \hat{E}\,u,\, \hat{F}\,v\rangle = 0$ for all $u, v \in C$.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
lemma error_subspaces_orthogonal {n t : ℕ} {C : Submodule ℂ (Hn n)}
    (h_nondeg : IsNondegenerate n C t)
    (E F : PauliString n) (hE : weight E ≤ t) (hF : weight F ≤ t) (h_neq : E ≠ F) :
    Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F)) := by

  have h_ortho : ∀ x y : Hn n, x ∈ C → y ∈ C → (pauliOp E x) ⬝ᵥ (star (pauliOp F y)) = 0 := by
    have := h_nondeg.2 E F hE hF h_neq;
    intro x y hx hy; replace this := congr_arg ( fun f => f y ) this; simp_all +decide ;
    have h_adj : (pauliOp E x) ⬝ᵥ (star (pauliOp F y)) = x ⬝ᵥ (star (pauliOpAdjoint E (pauliOp F y))) := by
      have h_adj : ∀ (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : EuclideanSpace ℂ (Fin n → Fin 2)), (A.mulVec x) ⬝ᵥ (star y) = x ⬝ᵥ (star (A.conjTranspose.mulVec y)) := by
        simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        exact fun A x y => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      convert h_adj ( pauliMatrix E ) x ( pauliOp F y ) using 1 <;> rfl
    have h_adj_zero : (pauliOpAdjoint E (pauliOp F y)) = (pauliOpAdjoint E (pauliOp F (codeProj C y))) := by
      rw [ codeProj_eq_self_of_mem hy ];
    have h_adj_zero : ∀ x y : Hn n, x ∈ C → (x ⬝ᵥ (star (codeProj C y))) = (x ⬝ᵥ (star y)) := by
      intro x y hx; rw [ codeProj_apply ] ; simp +decide [dotProduct] ;
      have h_adj_zero : ∀ x y : Hn n, x ∈ C → (x ⬝ᵥ (star (Submodule.starProjection C y))) = (x ⬝ᵥ (star y)) := by
        intro x y hx
        have h_perp : ∀ z ∈ Cᗮ, (x ⬝ᵥ (star z)) = 0 := by
          intro z hz; specialize hz x hx; simp_all +decide [dotProduct] ;
          simpa [ PiLp.inner_apply, mul_comm ] using congr_arg Star.star hz
        have h_split : (x ⬝ᵥ (star (Submodule.starProjection C y))) = (x ⬝ᵥ (star y)) - (x ⬝ᵥ (star (y - Submodule.starProjection C y))) := by
          simp +decide ;
        have h_mem : y - Submodule.starProjection C y ∈ Cᗮ :=
          Submodule.sub_starProjection_mem_orthogonal y
        have h_zero := h_perp _ h_mem
        simp only [WithLp.ofLp_sub] at h_zero
        rw [h_split, h_zero, sub_zero]
      exact h_adj_zero x y hx;
    specialize h_adj_zero x ( ( pauliOpAdjoint E ) ( ( pauliOp F ) ( codeProj C y ) ) ) hx; simp_all only [codeProj_apply,
      Submodule.coe_orthogonalProjection_apply, WithLp.ofLp_zero, star_zero, dotProduct_zero];
  intro x hx y hy;
  simp_all only [ne_eq, Submodule.mem_map]
  obtain ⟨w, h⟩ := hx
  obtain ⟨w_1, h_1⟩ := hy
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right_1⟩ := h_1
  subst right right_1
  apply h_ortho
  · simp_all only
  · simp_all only;


  /-
   proof in hsort:
  - show the family `(C.map (pauliOp E))` is pairwise disjoint (inf = ⊥) via orthogonality
  - use finrank of supremum over pairwise disjoint finite family
  - show each `pauliOp E` restricts to a linear equiv on `C` (invertible/unitary), hence
    `finrank (C.map (pauliOp E)) = finrank C`
  -/
