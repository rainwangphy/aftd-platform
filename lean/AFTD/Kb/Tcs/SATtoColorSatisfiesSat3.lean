import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorSatisfiesClause
import AFTD.Kb.Tcs.SATtoColorSat3
import AFTD.Kb.Tcs.SATtoColorClause

/-!
# SATtoColor.SatisfiesSat3

Topic: np_completeness   Node: 01d213dfba28

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.SatisfiesSat3`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An assignment $\mathrm{assign}$ \emph{satisfies} a 3-SAT instance $f$ if every
clause in the list $f$ is satisfied by $\mathrm{assign}$, i.e.\
$\mathrm{SatisfiesSat3}(\mathrm{assign}, f) = \texttt{true}$ iff
$\forall c \in f,\; \mathrm{SatisfiesClause}(\mathrm{assign}, c) = \texttt{true}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def SATtoColor.SatisfiesSat3 {V : Type} (assign : V → Bool) (f : Sat3 V) : Bool :=
  f.all (SatisfiesClause assign)
