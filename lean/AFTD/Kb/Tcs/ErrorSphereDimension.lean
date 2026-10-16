import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorSphere
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.IsNondegenerate
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.PauliErrorsLe
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.ErrorSubspacesOrthogonal
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule
import AFTD.Kb.Tcs.PauliBasis

/-!
# error_sphere_dimension

Topic: quantum   Node: f553fd2990a8

Provenance: helper lemma. TCSlib, `error_sphere_dimension`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 adapted; compiled here.

Dimension of the error sphere of a non-degenerate code. Let $C \le \mathcal{H}_n$ be a code on $n$ qubits that is non-degenerate for $t$ errors,
meaning it satisfies the Knill--Laflamme condition $P_C E^\dagger F P_C = \lambda_{EF}
P_C$ for all Pauli strings $E,F$ of weight at most $t$ and moreover $P_C E^\dagger F P_C
= 0$ whenever $E \neq F$. Then the error sphere $\mathrm{ES}(C,t) =
\bigvee_{\mathrm{wt}(p)\le t} \hat{p}(C)$ has dimension
\[
\dim_{\mathbb{C}} \mathrm{ES}(C,t) = |\mathcal{E}(n,t)| \cdot \dim_{\mathbb{C}} C,
\]
where $\mathcal{E}(n,t)$ is the set of Pauli strings of weight at most $t$.
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
lemma error_sphere_dimension {n t : ℕ} {C : Submodule ℂ (Hn n)}
    (h_nondeg : IsNondegenerate n C t) :
    Module.finrank ℂ (ErrorSphere n t C) =
    (PauliErrorsLe n t).card * Module.finrank ℂ C := by
  /-
  proof strat:
  - show the family `(C.map (pauliOp E))` is pairwise disjoint (inf = ⊥) via orthogonality
  - use finrank of supremum over pairwise disjoint finite family
  - show each `pauliOp E` restricts to a linear equiv on `C` (invertible/unitary), hence
    `finrank (C.map (pauliOp E)) = finrank C`
  -/
  have h_dim_sum :
      ∀ (S : Finset (PauliString n)),
        (∀ E ∈ S, weight E ≤ t) →
          Module.finrank ℂ (↥(Finset.sup S (fun E => C.map (pauliOp E))))
            = Finset.card S * Module.finrank ℂ C := by
    intro S hS
    induction' S using Finset.induction with E S hES ih
    · simp +decide
    · have h_orthogonal :
          Submodule.IsOrtho (C.map (pauliOp E))
            (Finset.sup S (fun E => C.map (pauliOp E))) := by
        have h_orthogonal :
            ∀ F ∈ S, Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F)) := by
          intro F hF
          apply error_subspaces_orthogonal h_nondeg E F
            (hS E (Finset.mem_insert_self E S))
            (hS F (Finset.mem_insert_of_mem hF))
          simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, ne_eq]
          obtain ⟨left, right⟩ := hS
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
        have h_orthogonal_sup :
            ∀ (T : Finset (PauliString n)),
              (∀ F ∈ T, Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F))) →
              Submodule.IsOrtho (C.map (pauliOp E))
                (Finset.sup T (fun F => C.map (pauliOp F))) := by
          intro T hT
          induction T using Finset.induction <;> aesop
        exact h_orthogonal_sup S h_orthogonal

      have h_dim_sum :
          Module.finrank ℂ (↥(C.map (pauliOp E) ⊔ Finset.sup S (fun E => C.map (pauliOp E))))
            =
          Module.finrank ℂ (↥(C.map (pauliOp E)))
            + Module.finrank ℂ (↥(Finset.sup S (fun E => C.map (pauliOp E)))) := by
        rw [← Submodule.finrank_sup_add_finrank_inf_eq]
        simp +zetaDelta at *
        exact h_orthogonal.disjoint.eq_bot

      convert h_dim_sum using 1
      · rw [Finset.sup_insert]
      ·
        rw [Finset.card_insert_of_notMem hES, ih (fun E hE => hS E (Finset.mem_insert_of_mem hE))]

        have h_inv : Function.Injective (pauliOp E) := by
          have h_inv : Invertible (pauliMatrix E) := by
            have h_inv : (pauliMatrix E).conjTranspose * pauliMatrix E = 1 := by
              ext i j
              simp +decide [Matrix.mul_apply, pauliMatrix]
              -- Since these are Pauli matrices, we know that their product is zero unless i = j.
              have h_pauli_prod :
                  ∀ k : Fin n,
                    ∑ x : Fin 2,
                      (starRingEnd ℂ ((E k).toMatrix x (i k))) * ((E k).toMatrix x (j k))
                        = if i k = j k then 1 else 0 := by
                intro k
                rcases E k with (_ | _ | _ | _) <;>
                  norm_num [Fin.sum_univ_succ, Matrix.mul_apply, PauliBasis.toMatrix]
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaI] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaX] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaY] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaZ] <;> tauto
              simp +decide [← Finset.prod_mul_distrib]
              rw [show
                (∑ x : Fin n → Fin 2,
                  ∏ x_1 : Fin n,
                    (starRingEnd ℂ) ((E x_1 |> PauliBasis.toMatrix) (x x_1) (i x_1)) *
                      (E x_1 |> PauliBasis.toMatrix) (x x_1) (j x_1))
                  =
                ∏ k : Fin n,
                  (∑ x : Fin 2,
                    (starRingEnd ℂ) ((E k |> PauliBasis.toMatrix) x (i k)) *
                      (E k |> PauliBasis.toMatrix) x (j k)) from by
                  exact
                    Eq.symm
                      (Fintype.prod_sum fun i_1 j_1 =>
                        (starRingEnd ℂ) ((E i_1).toMatrix j_1 (i i_1)) *
                          (E i_1).toMatrix j_1 (j i_1))]
              ·
                simp +decide [h_pauli_prod, Matrix.one_apply]
                by_cases hij : i = j <;> simp +decide [hij, Finset.prod_ite]
                exact Function.ne_iff.mp hij
            exact _root_.invertibleOfLeftInverse _ _ h_inv
          intro x y hxy
          have h_eq : (pauliMatrix E).mulVec x.ofLp = (pauliMatrix E).mulVec y.ofLp := by
            simpa [pauliOp] using congrArg WithLp.ofLp hxy
          have h_of : x.ofLp = y.ofLp := by
            simpa using congr_arg (fun z => ((pauliMatrix E)⁻¹).mulVec z) h_eq
          exact WithLp.ofLp_injective _ h_of

        have h_dim_map :
            ∀ (f : Hn n →ₗ[ℂ] Hn n), Function.Injective f →
              ∀ (C : Submodule ℂ (Hn n)),
                Module.finrank ℂ (↥(C.map f)) = Module.finrank ℂ C := by
          intro f hf C
          have h_iso : C ≃ₗ[ℂ] C.map f := by
            exact Submodule.equivMapOfInjective f hf C
          exact LinearEquiv.finrank_eq h_iso.symm

        have h_map_finrank :
            Module.finrank ℂ (↥(Submodule.map (pauliOp E) C)) = Module.finrank ℂ C := by
          exact h_dim_map _ h_inv _

        rw [h_map_finrank]
        ring

  exact h_dim_sum _ (fun E hE => (Finset.mem_filter.mp hE).2)
