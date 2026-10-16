import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.SPerpM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.DimVSub
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# g_le_two_card_C

Topic: quantum   Node: b520b519313f

Provenance: helper lemma. TCSlib, `g_le_two_card_C`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Correctable part contributes nothing to the operator count. Let $p$ be prime and let $S$ be an $\mathbb{F}_p$-subspace of the symplectic space $V =
\mathbb{F}_p^n \times \mathbb{F}_p^n$. Suppose $B$ and $C$ are disjoint subsets of the
coordinate set $\{0,\dots,n-1\}$, and that $B$ is correctable for $S$. Then
\[
g(S,\, B \cup C) \;\le\; 2\lvert C\rvert,
\]
where $g(S,M) = \dim_{\mathbb{F}_p}\!\bigl(S^{\perp}_M\bigr) -
\dim_{\mathbb{F}_p}\!\bigl(S_M\bigr)$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma g_le_two_card_C (S : Submodule (F p) (V n p)) (B C : Finset (Fin n))
    (h_disjoint : Disjoint B C) (hB : correctable S B) :
    g S (B ∪ C) ≤ 2 * C.card := by
      have h_g_def : g S (B ∪ C) = Module.finrank (F p) (S_perp_M S (B ∪ C)) - Module.finrank (F p) (S_M S (B ∪ C)) := by
        rfl;
      have h_S_perp_M_subset : S_perp_M S (B ∪ C) ≤ V_sub (p:=p) (B ∪ C) := by
        exact inf_le_right;

      set U : Submodule (F p) (V n p) := S_perp_M S (B ∪ C);

      set r_C : U →ₗ[F p] V_sub (p:=p) C := (r_E C).comp (Submodule.subtype U);
      have h_kernel_r_C : LinearMap.ker r_C = Submodule.comap (Submodule.subtype U) (V_sub (p:=p) B) := by
        ext v
        simp [r_C, r_E];
        apply Iff.intro
        intro h_zero
        have h_support : ∀ i, i ∉ B → (v : V n p).1 i = 0 ∧ (v : V n p).2 i = 0 := by
          intro i hi; specialize h_S_perp_M_subset v.2; simp_all +decide [ V_sub ] ;
          by_cases hi' : i ∈ C <;> try simp_all +decide [ Subtype.ext_iff ];
          have hz := congrArg Subtype.val h_zero
          simp only [ZeroMemClass.coe_zero, Prod.mk_eq_zero] at hz
          exact ⟨ by simpa [ hi' ] using congr_fun hz.1 i, by simpa [ hi' ] using congr_fun hz.2 i ⟩
        exact (by
        exact fun i hi => by specialize h_support i hi; simp_all only [Submodule.mk_eq_zero, Prod.mk_eq_zero, and_self,
          U];)
        intro h_support
        have h_zero : ∀ i ∈ C, (v : V n p).1 i = 0 ∧ (v : V n p).2 i = 0 := by
          exact fun i hi => h_support i ( Finset.disjoint_right.mp h_disjoint hi )
        exact (by
        ext i; simp_all only [ite_self, ZeroMemClass.coe_zero, Prod.fst_zero, Pi.zero_apply, U];
        by_cases hi : i ∈ C <;> simp +decide [ hi, h_zero ])

      have h_S_perp_B_subset_S : Submodule.comap (Submodule.subtype U) (V_sub (p:=p) B) ≤ Submodule.comap (Submodule.subtype U) S := by
        intro x hx; exact (by
        have := hB ( show x.1 ∈ sym_orth S ⊓ V_sub B from ?_ ) ; simp_all only [Submodule.mem_comap,
          Submodule.subtype_apply, U, r_C];
        exact ⟨ x.2.1, hx ⟩);
      have h_dim_U_le : Module.finrank (F p) U ≤ Module.finrank (F p) (LinearMap.range r_C) + Module.finrank (F p) (Submodule.comap (Submodule.subtype U) S) := by
        have := LinearMap.finrank_range_add_finrank_ker r_C;
        rw [ ← this ];
        exact add_le_add_right ( Submodule.finrank_mono <| h_kernel_r_C ▸ h_S_perp_B_subset_S ) _;
      have h_dim_r_C_U_le : Module.finrank (F p) (LinearMap.range r_C) ≤ 2 * C.card := by
        exact le_trans ( Submodule.finrank_le _ ) ( by erw [ dim_V_sub ] );
      have h_dim_S_inter_V_B_union_C_le : Module.finrank (F p) (Submodule.comap (Submodule.subtype U) S) ≤ Module.finrank (F p) (S_M S (B ∪ C)) := by
        rw [ ← Submodule.finrank_map_subtype_eq ];
        refine' Submodule.finrank_mono _;
        simp +zetaDelta at *;
        exact fun x hx => ⟨ hx.2, h_S_perp_M_subset hx.1 ⟩;
      exact h_g_def.symm ▸ Nat.sub_le_of_le_add ( by linarith )

/-
Definition of the number of logical qudits k.
-/
