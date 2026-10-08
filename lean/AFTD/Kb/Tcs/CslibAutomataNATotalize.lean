import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTSTotalize
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTotalizeNonsinkTrIff
import AFTD.Kb.Tcs.CslibLTSTotalizeNonsinkMtrIff
import AFTD.Kb.Tcs.CslibLTSInstTotalOptionTotalize

/-!
# Cslib.Automata.NA.totalize

Topic: automata   Node: 2e59d26c9e5f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.totalize`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Total.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`NA.totalize` makes the original NA total by replacing its LTS with `LTS.totalize` and its starting states with their lifted non-sink versions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Automata in
open Option in
variable {Symbol State : Type*} in
/-- `NA.totalize` makes the original NA total by replacing its LTS with `LTS.totalize` and its starting states with their lifted non-sink versions. -/
def Cslib.Automata.NA.totalize (na : NA State Symbol) : NA (Option State) Symbol where
  toLTS := na.toLTS.totalize
  start := some '' na.start
