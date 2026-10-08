import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# CodingTheory.Johnson.card_filter_add_two

Topic: information   Node: d77935237279

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.card_filter_add_two`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 adapted; compiled here.

Removing an element and its negation costs at most two. Let $S$ be a finite subset of an additive group $V$, and let $u \in S$. Then
\[
\abs{S} \le \abs{\{\, v \in S : v \neq u \text{ and } v \neq -u \,\}} + 2.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
open Classical in
attribute [local instance] Classical.dec in
lemma CodingTheory.Johnson.card_filter_add_two {V : Type*} [AddGroup V]
    (S : Finset V) (u : V) (_hu : u ∈ S) :
    S.card ≤ (S.filter (fun v => v ≠ u ∧ v ≠ -u)).card + 2 := by
  classical
  suffices (S.filter (fun v => ¬(v ≠ u ∧ v ≠ -u))).card ≤ 2 by
    have := Finset.card_filter_add_card_filter_not (s := S) (p := fun v => v ≠ u ∧ v ≠ -u)
    omega
  have hsub : S.filter (fun v => ¬(v ≠ u ∧ v ≠ -u)) ⊆ {u, -u} := by
    intro v hv
    simp only [Finset.mem_filter, not_and_or, not_ne_iff] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_insert_le u {-u}) (by simp))
