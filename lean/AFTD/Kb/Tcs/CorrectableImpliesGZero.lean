import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.SymOrth

/-!
# correctable_implies_g_zero

Topic: quantum   Node: 5d2e905410fe

Provenance: helper lemma. TCSlib, `correctable_implies_g_zero`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Correctable coordinate sets carry no supportable logical operators. Fix a prime $p$, let $V = \bbf_p^n \times \bbf_p^n$ be equipped with the symplectic form
$\omega\big((x,z),(x',z')\big) = \sum_{i} (x_i z'_i - z_i x'_i)$, and let $S \le V$ be a
subspace with symplectic orthogonal complement $S^{\perp_\omega} = \{v \in V :
\omega(v,s) = 0 \text{ for all } s \in S\}$. Let $M \subseteq \{0,1,\dots,n-1\}$ be a
set of coordinates, write $V_M$ for the subspace of vectors supported on $M$, and set
$S_M = S \cap V_M$ and $S^{\perp}_M = S^{\perp_\omega} \cap V_M$. If $M$ is correctable
for $S$ — meaning every vector of $S^{\perp_\omega}$ supported on $M$ already lies in
$S$, i.e. $S^{\perp}_M \le S$ — then $g(S,M) = \dim_{\bbf_p}(S^{\perp}_M) -
\dim_{\bbf_p}(S_M) = 0$.
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
lemma correctable_implies_g_zero (S : Submodule (F p) (V n p)) (M : Finset (Fin n))
    (h : correctable S M) : g S M = 0 := by
      have h_sub : sym_orth S ⊓ V_sub (p:=p) M ≤ S_M S M := by
        exact fun x hx => ⟨ h hx, hx.2 ⟩;
      refine' Nat.sub_eq_zero_of_le _;
      apply_rules [ Submodule.finrank_mono ]

/-
Checking if cleaning_dimension_identity exists.
-/
