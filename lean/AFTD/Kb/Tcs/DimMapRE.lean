import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.KerRE
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymBApply

/-!
# dim_map_r_E

Topic: quantum   Node: 2f33967abe2c

Provenance: helper lemma. TCSlib, `dim_map_r_E`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Rank of a restricted subspace of $\mathbb{F}_p^n \times \mathbb{F}_p^n$. Fix a prime $p$ and an integer $n \ge 0$, and let $V = \mathbb{F}_p^n \times
\mathbb{F}_p^n$. For a set $E$ of coordinates, let $r_E \colon V \to V$ be the
restriction map that leaves each coordinate in $E$ unchanged and sets every coordinate
outside $E$ to zero, and for a set $C$ of coordinates let $V_C \le V$ be the subspace of
vectors supported on $C$. Then for every subspace $S \le V$,
\[
\dim_{\mathbb{F}_p} r_E(S) \;=\; \dim_{\mathbb{F}_p} S \;-\;
\dim_{\mathbb{F}_p}\!\bigl(S \cap V_{E^c}\bigr),
\]
where $E^c$ denotes the complement of $E$ among the $n$ coordinates.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Rank-nullity for restriction of S to E -/
lemma dim_map_r_E (S : Submodule (F p) (V n p)) (E : Finset (Fin n)) :
    Module.finrank (F p) ↥(S.map (r_E E)) = Module.finrank (F p) ↥S - Module.finrank (F p) ↥(S ⊓ V_sub (p:=p) (E_c E)) := by
      have h_rank_nullity : Module.finrank (F p) (↥(S.map (r_E E))) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker (r_E E))) := by
        have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), Module.finrank (F p) (↥(Submodule.map f S)) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker f)) := by
          intro f
          have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), Module.finrank (F p) (↥(Submodule.map f S)) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker f)) := by
            intro f
            have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), ∀ (U : Submodule (F p) (V n p)), Module.finrank (F p) (↥(Submodule.map f U)) = Module.finrank (F p) U - Module.finrank (F p) (↥(U ⊓ LinearMap.ker f)) := by
              intros f U
              have h_rank_nullity : Module.finrank (F p) (↥(Submodule.map f U)) = Module.finrank (F p) U - Module.finrank (F p) (↥(LinearMap.ker (f.comp (Submodule.subtype U)))) := by
                have := LinearMap.finrank_range_add_finrank_ker ( f.comp ( Submodule.subtype U ) );
                exact eq_tsub_of_add_eq <| by rw [ show LinearMap.range ( f ∘ₗ U.subtype ) = Submodule.map f U from by ext; aesop ] at this; linarith;
              convert h_rank_nullity using 3;
              rw [ ← Submodule.finrank_map_subtype_eq ];
              congr ; ext ;
              rename_i x
              simp_all only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map, LinearMap.coe_comp,
                Submodule.coe_subtype, Function.comp_apply, Submodule.subtype_apply, Subtype.exists, exists_and_left,
                exists_prop, exists_eq_right_right]
              obtain ⟨fst, snd⟩ := x
              apply Iff.intro
              · intro a
                simp_all only [and_self]
              · intro a
                simp_all only [and_self];
              · ext ; aesop;
              · ext ; aesop;
              · infer_instance
            exact h_rank_nullity f S;
          exact h_rank_nullity f;
        convert h_rank_nullity ( r_E E ) using 1;
      rwa [ show LinearMap.ker ( r_E E ) = V_sub ( E_c E ) from ?_ ] at h_rank_nullity;
      convert ker_r_E E using 1
      rfl

/-
Symplectic form of v (in V_M) and s is equal to symplectic form of v and r_E M s.
-/
