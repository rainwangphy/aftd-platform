import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.CodeK
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.GComplementCorrectable
import AFTD.Kb.Tcs.GLeTwoCardC
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# two_disjoint_correctable_sets_bound_logical_dimension

Topic: quantum   Node: ec512aab15ba

Provenance: helper lemma. TCSlib, `two_disjoint_correctable_sets_bound_logical_dimension`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Two disjoint correctable erasures bound the logical dimension. Work in the symplectic space $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$ over the prime field
$\bbf_p$, equipped with the symplectic form $\omega$, and let $S \le V$ be an isotropic
submodule, so that $\omega(u,v) = 0$ for all $u, v \in S$. Suppose $A, B \subseteq \{0,
1, \dots, n-1\}$ are two disjoint sets of coordinates, each correctable for $S$: every
vector of $S^{\perp_\omega}$ supported on $A$ lies in $S$, and likewise every vector of
$S^{\perp_\omega}$ supported on $B$ lies in $S$. Then the logical dimension $k(S) = n -
\dim S$ satisfies
\[
k(S) \;\le\; \bigl|\{0, 1, \dots, n-1\} \setminus (A \cup B)\bigr| \;=\; n - |A| - |B|.
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
/-- Lemma 5: Two disjoint correctable sets bound logical dimension -/
lemma two_disjoint_correctable_sets_bound_logical_dimension (S : Submodule (F p) (V n p)) (hS : IsIsotropic S)
    (A B : Finset (Fin n)) (h_disjoint : Disjoint A B)
    (hA : correctable S A) (hB : correctable S B) :
    code_k S ≤ (Finset.univ \ (A ∪ B)).card := by
      have h_g_Ac : g S (Finset.univ \ A) = 2 * (n - Module.finrank (F p) S) := by
        convert g_complement_correctable S hS A hA using 1;
        · simp [E_c, Finset.compl_eq_univ_sdiff]
        rw [ Nat.mul_sub_left_distrib ];
      have h_g_BC : g S (B ∪ (Finset.univ \ (A ∪ B))) ≤ 2 * (Finset.univ \ (A ∪ B)).card := by
        apply g_le_two_card_C;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₂ |>.2 ( Finset.mem_union_right _ hx₁ );
        · assumption;
      have h_BC_eq_Ac : B ∪ (Finset.univ \ (A ∪ B)) = Finset.univ \ A := by
        ext x; by_cases hx : x ∈ A <;> by_cases hx' : x ∈ B <;> simp +decide [ hx, hx' ] ;
        exact Finset.disjoint_left.mp h_disjoint hx hx';
      unfold code_k; simp_all only [Nat.ofNat_pos, mul_le_mul_iff_right₀, tsub_le_iff_right];
