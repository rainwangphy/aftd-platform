import AFTD.Prelude
import AFTD.Kb.Tcs.PauliErrorsLe
import AFTD.Kb.Tcs.CardPauliStringsExactSupport
import AFTD.Kb.Tcs.PauliStringsExactSupport
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.Support

/-!
# card_pauliErrorsLe

Topic: quantum   Node: d33948e96975

Provenance: helper lemma. TCSlib, `card_pauliErrorsLe`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 adapted; compiled here.

Cardinality of the bounded-weight Pauli error set. For natural numbers $n$ and $t$, the number of Pauli strings of length $n$ whose weight
is at most $t$ is
\[
|\mathcal{E}(n,t)| \;=\; \sum_{j=0}^{t} \binom{n}{j}\, 3^{\,j}.
\]
Here a Pauli string is a function $p : \mathrm{Fin}\,n \to \{I,X,Y,Z\}$, and its weight
$\mathrm{wt}(p)$ is the number of coordinates $i$ with $p(i) \neq I$; the sum counts,
for each $j \le t$, the $\binom{n}{j}$ choices of a weight-$j$ support together with the
$3^{j}$ assignments of a non-identity Pauli to each chosen coordinate.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
/-- Clean Quantum Hamming counting identity. -/
theorem card_pauliErrorsLe (n t : ℕ) :
    (PauliErrorsLe n t).card = ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j := by
  classical
  /-
   proof outline:
  - partition by `j = weight p`
  - partition by exact support `S` with `S.card = j`
  - count supports: `card (powersetCard j univ) = n.choose j`
  - each support contributes `3^j` by `card_pauliStringsExactSupport`
  -/
  have h_union : PauliErrorsLe n t = Finset.biUnion (Finset.range (t + 1)) (fun j => Finset.biUnion (Finset.powersetCard j (Finset.univ : Finset (Fin n))) (fun S => pauliStringsExactSupport S)) := by
    ext p; simp [PauliErrorsLe, pauliStringsExactSupport];
    exact Iff.rfl;
  rw [ h_union, Finset.card_biUnion, Finset.sum_congr rfl ];
  · intro j hj; rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => card_pauliStringsExactSupport x ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ Finset.card_univ ];
    · intro S hS T hT hST; simp_all +decide [ Finset.disjoint_left, pauliStringsExactSupport ] ;
  · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
    unfold pauliStringsExactSupport;
    intro a x a_1 a_2 x_1 a_3
    subst a_1 a_3
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    subst a_2
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [not_true_eq_false];
