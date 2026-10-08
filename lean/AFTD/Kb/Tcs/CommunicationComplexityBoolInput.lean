import AFTD.Prelude

/-!
# CommunicationComplexity.BoolInput

Topic: communication   Node: bf0ef14c1e8b

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.BoolInput`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{BoolInput}(n)$ is the type of $n$-bit Boolean inputs, defined as the function
type $\mathrm{Fin}\,n \to \mathrm{Bool}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The type of `n`-bit Boolean inputs. -/
abbrev CommunicationComplexity.BoolInput (n : Nat) := Fin n → Bool
