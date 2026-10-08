import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify
import AFTD.Kb.Tcs.SchnorrCommit
import AFTD.Kb.Tcs.SchnorrRespond

/-!
# Schnorr.schnorr_completeness

Topic: cryptography   Node: 1bbde28e6fd5

Provenance: formalization of a published result. Source: Completeness of the Schnorr identification protocol, as formalized in TCSlib (`Schnorr.schnorr_completeness`). Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Cryptography/SchnorrProtocol.lean (Apache-2.0); 1 verbatim; compiled here.

Completeness of the Schnorr identification protocol. Let $q$ be a prime, let $G$ be a commutative group, and let $g \in G$ be an element of
order $q$. For any witness $w$, randomness $r$, and challenge $c$ in $\mathbb{Z}_q$, the
honest transcript — commitment $a = g^{r}$, challenge $c$, and response $s = r + c\,w$ —
is accepted by the verifier against the public key $\mathit{pk} = g^{w}$; that is,
\[
  g^{\,s} \;=\; a \cdot \mathit{pk}^{\,c},
\]
where each exponent is taken via the canonical lift of the corresponding element of
$\mathbb{Z}_q$ to $\mathbb{N}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {G : Type*} [CommGroup G] in
variable {q : ℕ} [Fact q.Prime] in
variable (g : G) in
/-- **Completeness**: for any witness `w`, randomness `r`, and challenge `c` in `ZMod q`, with generator `g` of order `q`, the honest transcript `(g^r, c, r + c·w)` satisfies the verifier equation `g ^ (r + c·w).val = g^r.val * (g^w.val)^c.val`. -/
theorem Schnorr.schnorr_completeness
    (hg : orderOf g = q) (w r c : ZMod q) :
    Verify g (g ^ w.val) (commit g r) c (respond w r c) := by
  simp only [Verify, commit, respond]
  rw [← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, hg]
  have h1 : (r + c * w).val ≡ r.val + (c * w).val [MOD q] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have h2 : (c * w).val ≡ w.val * c.val [MOD q] := by
    rw [ZMod.val_mul, mul_comm]
    exact Nat.mod_modEq _ _
  exact h1.trans (h2.add_left _)
