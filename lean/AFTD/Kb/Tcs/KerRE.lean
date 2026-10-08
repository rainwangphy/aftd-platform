import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.RE

/-!
# ker_r_E

Topic: quantum   Node: 4b9a8d5c16e7

Provenance: helper lemma. TCSlib, `ker_r_E`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Kernel of the coordinate restriction map. Fix a prime $p$ and let $V = \bbf_p^n \times \bbf_p^n$. For a subset $E \subseteq
\{1,\dots,n\}$, let $r_E \colon V \to V_E$ be the restriction map that keeps the
coordinates indexed by $E$ and sets all others to zero. Then the kernel of $r_E$ is the
support submodule $V_{E^c}$ consisting of those vectors whose support lies in the
complement $E^c = \{1,\dots,n\} \setminus E$; that is, $r_E$ annihilates exactly the
vectors that vanish on every coordinate in $E$.
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
/-- Kernel of r_E is V_{E^c} -/
lemma ker_r_E (E : Finset (Fin n)) :
    LinearMap.ker (r_E (p:=p) E) = V_sub (p:=p) (Finset.univ \ E) := by
  classical
  ext x
  constructor
  · intro hx
    have hx0 : (r_E (p:=p) E) x = 0 := by
      simpa [LinearMap.mem_ker] using hx

    have hxval : ((r_E (p:=p) E) x : V n p) = 0 :=
      congrArg Subtype.val hx0

    have hx1fun :
        (fun i : Fin n => if i ∈ E then x.1 i else 0) = 0 := by
      simpa [r_E] using congrArg Prod.fst hxval
    have hx2fun :
        (fun i : Fin n => if i ∈ E then x.2 i else 0) = 0 := by
      simpa [r_E] using congrArg Prod.snd hxval

    intro i hi
    have hiE : i ∈ E := by
      simpa [Finset.mem_sdiff, Finset.mem_univ] using hi
    constructor
    · have hx1i : (if i ∈ E then x.1 i else 0) = 0 :=
        congrArg (fun f => f i) hx1fun
      simpa [hiE] using hx1i
    · have hx2i : (if i ∈ E then x.2 i else 0) = 0 :=
        congrArg (fun f => f i) hx2fun
      simpa [hiE] using hx2i

  · intro hx

    have hfx : (r_E (p:=p) E) x = 0 := by
      ext i <;> by_cases hi : i ∈ E
      ·
        have hnot : i ∉ (Finset.univ \ E) := by
          simp [Finset.mem_sdiff, Finset.mem_univ, hi]

        simpa [r_E, hi] using (hx i hnot).1
      ·
        simp [r_E, hi]
      ·
        have hnot : i ∉ (Finset.univ \ E) := by
          simp [Finset.mem_sdiff, Finset.mem_univ, hi]
        simpa [r_E, hi] using (hx i hnot).2
      ·
        simp [r_E, hi]

    simpa [LinearMap.mem_ker] using hfx


/-
Defining complement of E.
-/
