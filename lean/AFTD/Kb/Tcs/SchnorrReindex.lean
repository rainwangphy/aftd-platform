import AFTD.Prelude

/-!
# Schnorr.reindex

Topic: cryptography   Node: 031b6419836f

Provenance: formalization of a published result. Source: TCSlib, `Schnorr.reindex`. Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

For fixed $w, c \in \mathbb{Z}_q$, define the bijection
$\sigma_{w,c} : \mathbb{Z}_q \xrightarrow{\;\sim\;} \mathbb{Z}_q$ by
$r \mapsto r + c \cdot w$, with inverse $s \mapsto s - c \cdot w$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- Reindexing bijection on `ZMod q`: `r ↦ r + c·w`, inverse `s ↦ s - c·w`. -/
def Schnorr.reindex (w c : ZMod q) : ZMod q ≃ ZMod q where
  toFun r := r + c * w
  invFun s := s - c * w
  left_inv := by intro r; ring
  right_inv := by intro s; ring
