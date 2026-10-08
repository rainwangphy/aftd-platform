import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm

/-!
# sym_form_smul_right

Topic: quantum   Node: ce3dd0dcf0ef

Provenance: helper lemma. TCSlib, `sym_form_smul_right`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Additivity of the symplectic form in the first argument. Let $p$ be prime and work over the space $V = \bbf_p^n \times \bbf_p^n$ equipped with
the symplectic form $\omega(u,v) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$, where $u =
(x,z)$ and $v = (x',z')$. Then for all $x, y, z \in V$,
\[
\omega(x + y, z) = \omega(x, z) + \omega(y, z).
\]

Fix a prime $p$ and a natural number $n$, and let $V = \bbf_p^n \times \bbf_p^n$, where
$\bbf_p = \bbz/p\bbz$. Equip $V$ with the symplectic form $\omega(u,v) =
\sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$ for $u = (x,z)$ and $v = (x',z')$. Then $\omega$
is additive in its second argument: for all $x, y, z \in V$, \[ \omega(x,\, y + z) =
\omega(x,y) + \omega(x,z). \]

Let $p$ be prime and work over the prime field $\bbf_p$, with $V = \bbf_p^n \times
\bbf_p^n$ carrying the symplectic form $\omega$ given by $\omega(u,v) =
\sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$ for $u=(x,z)$ and $v=(x',z')$. Then for every
scalar $c \in \bbf_p$ and all $x, y \in V$,
\[
\omega(c\,x,\, y) \;=\; c\,\omega(x, y),
\]
where $c\,x$ denotes the coordinatewise scalar multiplication of $x$ by $c$.

Let $p$ be a prime, and equip $V = \bbf_p^n \times \bbf_p^n$ with the symplectic form
$\omega(u,v) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$, where $u = (x,z)$ and $v =
(x',z')$. Then for every scalar $c \in \bbf_p$ and all $x, y \in V$,
\[
\omega(x, c\,y) \;=\; c\,\omega(x, y),
\]
where $c\,y$ denotes componentwise scalar multiplication.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma sym_form_smul_right (c : F p) (x y : V n p) :
    sym_form (n:=n) (p:=p) x (c • y) = c * sym_form (n:=n) (p:=p) x y := by
  classical
  unfold sym_form

  have h1 :
      (∑ i : Fin n, x.1 i * (c * y.2 i))
        = c * (∑ i : Fin n, x.1 i * y.2 i) := by
    change (Finset.univ.sum (fun i : Fin n => x.1 i * (c * y.2 i)))
        = c * (Finset.univ.sum (fun i : Fin n => x.1 i * y.2 i))
    have hs :
        (fun i : Fin n => x.1 i * (c * y.2 i))
          = (fun i : Fin n => c * (x.1 i * y.2 i)) := by
      funext i
      simp [mul_left_comm]
    rw [hs]
    rw [← Finset.mul_sum]


  have h2 :
      (∑ i : Fin n, x.2 i * (c * y.1 i))
        = c * (∑ i : Fin n, x.2 i * y.1 i) := by
    change (Finset.univ.sum (fun i : Fin n => x.2 i * (c * y.1 i)))
        = c * (Finset.univ.sum (fun i : Fin n => x.2 i * y.1 i))
    have hs :
        (fun i : Fin n => x.2 i * (c * y.1 i))
          = (fun i : Fin n => c * (x.2 i * y.1 i)) := by
      funext i
      simp [mul_assoc, mul_comm]
    rw [hs]
    rw [← Finset.mul_sum]


  simp [h1, h2, mul_sub]
