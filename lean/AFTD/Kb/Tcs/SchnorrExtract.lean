import AFTD.Prelude

/-!
# Schnorr.extract

Topic: cryptography   Node: d973bc2c8b44

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.extract`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Given two challenges $c_1, c_2$ and corresponding responses $s_1, s_2$ in
$\mathbb{Z}_q$, the extractor returns
\[
  \frac{s_1 - s_2}{c_1 - c_2} \;\in\; \mathbb{Z}_q.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Two-transcript witness extractor: `(s₁ - s₂) / (c₁ - c₂)` in `ZMod q`. -/
def Schnorr.extract (c₁ c₂ s₁ s₂ : ZMod q) : ZMod q :=
  ((s₁ - s₂) / (c₁ - c₂) : ZMod q)
