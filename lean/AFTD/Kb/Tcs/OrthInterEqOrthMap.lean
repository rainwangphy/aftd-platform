import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.REV
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormLeftRestrict
import AFTD.Kb.Tcs.SymOrth

/-!
# orth_inter_eq_orth_map

Topic: quantum   Node: 1b50d2455190

Provenance: helper lemma. TCSlib, `orth_inter_eq_orth_map`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Restricting to a support before taking the symplectic complement. Fix a prime $p$ and work in the symplectic space $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$
equipped with the form $\omega\big((x,z),(x',z')\big) = \sum_{i=0}^{n-1}(x_i z'_i - z_i
x'_i)$, and for a subset $M \subseteq \{0,\dots,n-1\}$ let $V_M$ be the submodule of
vectors whose support lies in $M$ and let $r_M \colon V \to V$ be the map that zeroes
every coordinate outside $M$ and fixes those in $M$. Then for every $\bbf_p$-subspace $S
\le V$,
\[
S^{\perp_\omega} \cap V_M \;=\; \big(r_M(S)\big)^{\perp_\omega} \cap V_M,
\]
where $r_M(S)$ denotes the image of $S$ under $r_M$ and $(\cdot)^{\perp_\omega}$ the
orthogonal complement with respect to $\omega$.
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
/-- Orthogonal intersection lemma -/
lemma orth_inter_eq_orth_map (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    sym_orth (n:=n) (p:=p) S ⊓ V_sub (p:=p) M
      = sym_orth (n:=n) (p:=p) (S.map (r_E_V (n:=n) (p:=p) M)) ⊓ V_sub (p:=p) M := by
  classical
  ext v
  constructor
  · rintro ⟨hvS, hvM⟩
    refine ⟨?_, hvM⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : sym_form (n:=n) (p:=p) s v = 0 := by
      simpa using hvS s hs
    have hpair :
        sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v
          = sym_form (n:=n) (p:=p) s v :=
      sym_form_left_restrict (n:=n) (p:=p) M s v hvM

    simp [LinearMap.BilinForm.IsOrtho, symB_apply, hpair]
    exact hs0

  · rintro ⟨hvMap, hvM⟩
    refine ⟨?_, hvM⟩
    intro s hs
    have h0 : sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v = 0 := by
      simpa using hvMap ((r_E_V (n:=n) (p:=p) M) s) (Submodule.mem_map_of_mem hs)
    have hpair :
        sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v
          = sym_form (n:=n) (p:=p) s v :=
      sym_form_left_restrict (n:=n) (p:=p) M s v hvM
    -- goal is sym_form s v = 0
    simpa [hpair] using h0

/-
Checking if S_M and S_perp_M are already defined.
-/
