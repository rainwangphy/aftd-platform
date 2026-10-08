import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolExists
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run

Topic: communication   Node: 5c35a30b7d56

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conversion to binary protocol preserves output. Let $p$ be a finite-message deterministic two-party protocol over input types $X$ and
$Y$ with output type $\alpha$, and let $q$ be the binary protocol obtained by converting
$p$ (encoding each message drawn from a finite nonempty type $\beta$ as $\lceil \log_2
\abs{\beta} \rceil$ bits). Then $q$ computes the same function as $p$: for every pair of
inputs $x \in X$ and $y \in Y$, running $q$ on $(x, y)$ returns the same value in
$\alpha$ as running $p$ on $(x, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The binary protocol obtained from a finite-message protocol has the same outcome function. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run (p : Protocol X Y α) :
    (toProtocol p).run = p.run :=
  (toProtocol_exists p).choose_spec.1
