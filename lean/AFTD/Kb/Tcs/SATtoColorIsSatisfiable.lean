import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorSatisfiesSat3
import AFTD.Kb.Tcs.SATtoColorSat3

/-!
# SATtoColor.IsSatisfiable

Topic: np_completeness   Node: 2004f9cd2fa9

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.IsSatisfiable`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A 3-SAT instance $f$ is \emph{satisfiable} if there exists a Boolean
assignment that satisfies it:
\[
  \mathrm{IsSatisfiable}(f)
  \;:=\;
  \exists\,\mathrm{assign}: V \to \mathrm{Bool},\;
  \mathrm{SatisfiesSat3}(\mathrm{assign}, f) = \texttt{true}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
noncomputable def SATtoColor.IsSatisfiable {V : Type} (f : Sat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesSat3 assign f = true

-- Some examples to test definitions:
