import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.VSub

/-!
# extendFromC

Topic: quantum   Node: 011080a748ae

Provenance: formalization of a published result. Source: TCSlib, `extendFromC`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

The linear map $(C \to \mathbb{F}_p) \times (C \to \mathbb{F}_p) \to V_C$ that extends a pair of
functions on $C$ to a vector of $V$ by setting all coordinates outside $C$ to zero.
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
noncomputable def extendFromC (C : Finset (Fin n)) :
    (C → F p) × (C → F p) →ₗ[F p] V_sub (p:=p) C where
  toFun := fun ⟨f, g⟩ =>
    ⟨ ((fun i => if h : i ∈ C then f ⟨i, h⟩ else 0),
       (fun i => if h : i ∈ C then g ⟨i, h⟩ else 0)),
      by
        intro j hj
        constructor <;> simp [hj] ⟩
  map_add' := by
    classical
    rintro ⟨f1, g1⟩ ⟨f2, g2⟩
    apply Subtype.ext
    ext i <;> by_cases hi : i ∈ C <;> simp [hi]
  map_smul' := by
    classical
    intro r x
    rcases x with ⟨f, g⟩
    apply Subtype.ext
    ext i <;> by_cases hi : i ∈ C <;> simp [hi]
