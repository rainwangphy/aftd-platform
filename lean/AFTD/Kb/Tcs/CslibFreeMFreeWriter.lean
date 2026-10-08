import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMWriterF
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad

/-!
# Cslib.FreeM.FreeWriter

Topic: computability   Node: 5bc4d3f6ff1f

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeWriter`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Writer monad implemented via the `FreeM` monad construction. This provides a more efficient implementation than the traditional `WriterT` transformer, as it avoids buffering the log.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
/-- Writer monad implemented via the `FreeM` monad construction. This provides a more efficient implementation than the traditional `WriterT` transformer, as it avoids buffering the log. -/
abbrev Cslib.FreeM.FreeWriter (ω : Type u) := FreeM (WriterF ω)
