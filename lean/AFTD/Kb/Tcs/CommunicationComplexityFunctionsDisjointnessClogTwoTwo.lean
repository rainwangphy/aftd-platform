import AFTD.Prelude

/-!
# CommunicationComplexity.Functions.Disjointness.clog_two_two

Topic: communication   Node: 7acb1d62fb68

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Disjointness.clog_two_two`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ceiling logarithm of two in base two. The ceiling base-$2$ logarithm of $2$ equals $1$: $\lceil \log_2 2 \rceil = 1$, i.e.\
$ Nat.clog\,2\,2 = 1$. This is a small numerical fact used in the
communication-complexity bounds of this module.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open scoped symmDiff in
/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
theorem CommunicationComplexity.Functions.Disjointness.clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl
