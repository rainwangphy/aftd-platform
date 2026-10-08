import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm

/-!
# sym_form_add_left

Topic: quantum   Node: 85f03c6b96f7

Provenance: helper lemma. TCSlib, `sym_form_add_left`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

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
lemma sym_form_add_left (x y z : V n p) :
    sym_form (n:=n) (p:=p) (x + y) z = sym_form (n:=n) (p:=p) x z + sym_form (n:=n) (p:=p) y z := by
  classical
  unfold sym_form
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h : (fun i : Fin n => (x.1 i + y.1 i) * z.2 i - (x.2 i + y.2 i) * z.1 i) =
           (fun i : Fin n => (x.1 i * z.2 i - x.2 i * z.1 i) + (y.1 i * z.2 i - y.2 i * z.1 i)) := by
    ext i
    ring
  rw [h]
  exact Finset.sum_add_distrib
