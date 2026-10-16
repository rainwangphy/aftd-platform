import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# dim_S_M_add_dim_S_M_c_le_dim_S

Topic: quantum   Node: 317953a52de2

Provenance: helper lemma. TCSlib, `dim_S_M_add_dim_S_M_c_le_dim_S`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Additivity bound for support-restricted subspaces. Fix a prime $p$ and an integer $n$, and let $S$ be a subspace of the ambient space $V =
\mathbb{F}_p^n \times \mathbb{F}_p^n$. For a subset $M \subseteq \{1,\dots,n\}$ with
complement $M^c$, write $S_M = S \cap V_M$ and $S_{M^c} = S \cap V_{M^c}$ for the
intersections of $S$ with the corresponding support subspaces. Then
\[
  \dim_{\mathbb{F}_p} S_M + \dim_{\mathbb{F}_p} S_{M^c} \le \dim_{\mathbb{F}_p} S.
\]
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
lemma dim_S_M_add_dim_S_M_c_le_dim_S (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) :
    Module.finrank (F p) (S_M S M) + Module.finrank (F p) (S_M S (E_c M)) ≤ Module.finrank (F p) S := by
      rw [ ← Submodule.finrank_sup_add_finrank_inf_eq ];
      have h_sum_subset : S_M S M ⊔ S_M S (E_c M) ≤ S := by
        exact sup_le ( inf_le_left ) ( inf_le_left );
      refine' le_trans ( add_le_add_left ( Submodule.finrank_mono h_sum_subset ) _ ) _;
      have hbot : S_M S M ⊓ S_M S (E_c M) = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        rw [Submodule.mem_bot]
        have h1 : ∀ i ∉ M, v.1 i = 0 ∧ v.2 i = 0 := hv.1.2
        have h2 : ∀ i ∉ E_c M, v.1 i = 0 ∧ v.2 i = 0 := hv.2.2
        have h3 : ∀ i, v.1 i = 0 ∧ v.2 i = 0 := fun i => by
          by_cases hi : i ∈ M
          · exact h2 i (by simp [E_c, hi])
          · exact h1 i hi
        exact Prod.ext (funext fun i => (h3 i).1) (funext fun i => (h3 i).2)
      simp [hbot]


/-
Formula for g(M) in terms of dimensions.
-/
