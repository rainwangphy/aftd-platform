import AFTD.Prelude

/-!
# Cslib.StatefulProcesses.Cfg.TrLabel

Topic: distributed   Node: 02a095cffe8e

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Cfg.TrLabel`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Network.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Transition labels for network configurations. These labels model what can be observed from execution, and thus hide internal computational details.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable [DecidableEq Pid] in
/-- Transition labels for network configurations. These labels model what can be observed from execution, and thus hide internal computational details. -/
inductive Cslib.StatefulProcesses.Cfg.TrLabel Pid Val SelLabel | local (p : Pid)
  | com (p : Pid) (q : Pid) (v : Val)
  | sel (p : Pid) (q : Pid) (l : SelLabel)
