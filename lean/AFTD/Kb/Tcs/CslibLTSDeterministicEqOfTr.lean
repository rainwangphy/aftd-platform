import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSDeterministic

/-!
# Cslib.LTS.Deterministic.eq_of_tr

Topic: computability   Node: d4314feaac03

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Deterministic.eq_of_tr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.Deterministic.eq_of_tr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
theorem Cslib.LTS.Deterministic.eq_of_tr {lts : LTS State Label} [lts.Deterministic]
    (htr : lts.Tr s1 μ s2) (htr' : lts.Tr s1 μ s2') : s2 = s2' :=
  Deterministic.deterministic s1 μ s2 s2' htr htr'
