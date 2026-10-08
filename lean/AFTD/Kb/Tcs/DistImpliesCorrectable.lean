import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.CodeDist
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.Supp
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.Wt

/-!
# dist_implies_correctable

Topic: quantum   Node: a78f0de02be1

Provenance: helper lemma. TCSlib, `dist_implies_correctable`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Erasure correction below the code distance. Let $p$ be prime and let $S$ be an $\mathbb{F}_p$-subspace of the symplectic space $V =
\mathbb{F}_p^n \times \mathbb{F}_p^n$, with code distance $d(S)$ and symplectic
orthogonal complement $S^{\perp_\omega}$. If $E \subseteq \{0,\dots,n-1\}$ is a set of
erased coordinates with $|E| < d(S)$, then $E$ is correctable for $S$: every $v \in V_E
\cap S^{\perp_\omega}$ already lies in $S$.
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
/-- An erasure set `E` is correctable whenever its size is strictly less than the code distance. -/
lemma dist_implies_correctable (S : Submodule (F p) (V n p)) (E : Finset (Fin n))
    (h : E.card < code_dist S) : correctable S E := by
      intro v hv;
      have h_weight : ∀ v ∈ sym_orth S ⊓ V_sub E, v∉ S → code_dist S ≤ wt v := by
        exact fun v hv hv' => Nat.sInf_le ⟨ v, hv.1, hv', rfl ⟩;
      have h_weight_le : ∀ v ∈ sym_orth S ⊓ V_sub E, v∉ S → wt v ≤ E.card := by
        intros v hv hv_not_in_S
        have h_support_subset : supp v ⊆ E := by
          exact fun i hi => Classical.not_not.1 fun hi' => by have := hv.2 i hi'; unfold supp at hi; simp_all only [Submodule.mem_inf,
            LinearMap.BilinForm.mem_orthogonal_iff, Prod.forall, and_imp, ne_eq, Set.toFinset_setOf,
            Finset.mem_filter, Finset.mem_univ, not_true_eq_false, or_self, and_false];
        exact Finset.card_le_card h_support_subset;
      exact Classical.not_not.1 fun hv' => not_lt_of_ge ( h_weight v hv hv' ) ( lt_of_le_of_lt ( h_weight_le v hv hv' ) h )

/-
Definition of g(M) with intermediate steps.
-/
