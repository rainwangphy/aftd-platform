import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliNZ
import AFTD.Kb.Tcs.PauliNZToBasis
import AFTD.Kb.Tcs.PauliString

/-!
# mkWithSupport

Topic: quantum   Node: 2675a038c0d9

Provenance: formalization of a published result. Source: TCSlib, `mkWithSupport`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Given a finset $S \subseteq \mathrm{Fin}\,n$ and an assignment $f : S \to \mathrm{PauliNZ}$,
constructs the Pauli string that equals $f(i).\mathrm{toBasis}$ on each $i \in S$ and equals $I$
elsewhere.
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
/-- Constructs a Pauli string with support exactly `S` and non-identity assignments given by `f`. -/
noncomputable def mkWithSupport {n : ℕ} (S : Finset (Fin n)) (f : S → PauliNZ) : PauliString n :=
  fun i => if h : i ∈ S then (f ⟨i, h⟩).toBasis else PauliBasis.I
