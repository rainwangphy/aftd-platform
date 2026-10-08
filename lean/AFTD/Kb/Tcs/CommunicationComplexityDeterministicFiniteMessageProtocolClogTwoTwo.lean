import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.clog_two_two

Topic: communication   Node: 76aa382dbe80

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.clog_two_two`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ceiling logarithm of two. The ceiling base-$2$ logarithm of $2$ equals $1$: $\lceil \log_2 2 \rceil = 1$, i.e.\ 
\texttt{Nat.clog 2 2 = 1}. This is a numeric fact used when comparing the
complexity of a binary protocol with its finite-message reformulation.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl
