import AFTD.Prelude

/-!
# CommunicationComplexity.Functions.Equality.clog_two_two

Topic: communication   Node: 55e75f01eaad

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Equality.clog_two_two`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ceiling logarithm of $2$ in base $2$. The base-$2$ ceiling logarithm of $2$ equals $1$: $\lceil \log_2 2 \rceil = 1$,
i.e.\ \texttt{Nat.clog 2 2 = 1}. This is a small arithmetic fact used in the
deterministic upper bound for the equality function.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
theorem CommunicationComplexity.Functions.Equality.clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl
