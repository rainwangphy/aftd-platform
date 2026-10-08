import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign

/-!
# CommunicationComplexity.boolSign_xor

Topic: communication   Node: 5870cc11430a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.boolSign_xor`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Boolean sign turns XOR into multiplication. Write $\mathrm{sgn} : \mathrm{Bool} \to \bbr$ for the Boolean sign map, which sends
$\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$. Then for all Boolean values $a, b$,
\[
  \mathrm{sgn}(a \oplus b) \;=\; \mathrm{sgn}(a)\,\mathrm{sgn}(b),
\]
where $a \oplus b$ denotes the exclusive-or of $a$ and $b$; equivalently, $\mathrm{sgn}$
is a homomorphism from $(\mathrm{Bool}, \oplus)$ to the multiplicative group $\{\pm
1\}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The sign of an exclusive or is the product of the signs: `boolSign (a xor b)` equals `boolSign a * boolSign b`. This is the one-bit case of the character identity `χ_S · χ_T = χ_{S △ T}` [OD14, §1.3]. -/
@[simp] lemma CommunicationComplexity.boolSign_xor (a b : Bool) :
    boolSign (Bool.xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> norm_num [boolSign]
