import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrCommit
import AFTD.Kb.Tcs.SchnorrHonest
import AFTD.Kb.Tcs.SchnorrReindex
import AFTD.Kb.Tcs.SchnorrRespond
import AFTD.Kb.Tcs.SchnorrSchnorrCompleteness
import AFTD.Kb.Tcs.SchnorrSimulate

/-!
# Schnorr.schnorr_hvzk

Topic: cryptography   Node: 7298ea2608a0

Provenance: formalization of a published result. Source: Honest-verifier zero knowledge of the Schnorr protocol, as formalized in TCSlib (`Schnorr.schnorr_hvzk`). Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Honest-verifier zero knowledge of the Schnorr protocol. Let $G$ be a commutative group, let $q$ be prime, and let $g \in G$ be an element of
order $q$, taken as the public generator. Fix a witness $w \in \bbz_q$ and a challenge
$c \in \bbz_q$, and let $\mathit{pk} = g^{w}$ be the associated public key. Then, as
functions $\bbz_q \to G \times \bbz_q \times \bbz_q$ of the prover's randomness $r$, the
honest transcript map $r \mapsto \big(g^{r},\, c,\, r + c\cdot w\big)$ coincides with
the simulator map fed the reindexed randomness $\sigma_{w,c}(r) = r + c\cdot w$, namely
$r \mapsto \big(g^{\sigma_{w,c}(r)}\cdot(\mathit{pk}^{\,c})^{-1},\, c,\,
\sigma_{w,c}(r)\big)$; that is, these two maps are equal.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- **HVZK (pointwise)**: for every fixed witness `w` and challenge `c`, with generator `g` of order `q`, the honest transcript function `r ↦ honest g w r c` and the simulator transcript function `s ↦ simulate g (g^w) c s` are equal as functions `ZMod q → Transcript G q` after the bijective reindexing `s = r + c·w` (i.e. `reindex w c`). -/
theorem Schnorr.schnorr_hvzk
    (hg : orderOf g = q) (w c : ZMod q) :
    (fun r => honest g w r c) =
    (fun r => simulate g (g ^ w.val) c (reindex w c r)) := by
  funext r
  simp only [honest, simulate, commit, respond, reindex]
  refine Prod.ext ?_ rfl
  rw [eq_mul_inv_iff_mul_eq]
  exact (schnorr_completeness g hg w r c).symm
