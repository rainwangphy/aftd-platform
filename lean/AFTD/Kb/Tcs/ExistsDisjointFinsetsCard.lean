import AFTD.Prelude

/-!
# exists_disjoint_finsets_card

Topic: quantum   Node: 9c6c3258eff6

Provenance: helper lemma. TCSlib, `exists_disjoint_finsets_card`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Existence of two disjoint sets of equal size. Let $n$ and $t$ be natural numbers with $2t \le n$. Then there exist two disjoint
subsets $A, B \subseteq \{1, \dots, n\}$, each of cardinality $t$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Choose disjoint finsets `A,B` of size `t` inside `Fin n`, assuming `2t ≤ n`. -/
lemma exists_disjoint_finsets_card (t : ℕ) (h : 2 * t ≤ n) :
    ∃ A B : Finset (Fin n), Disjoint A B ∧ A.card = t ∧ B.card = t := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have hU : U.card = n := by simp [U]

  have hsum : t + t ≤ U.card := by
    simpa [hU, two_mul] using h
  have htU : t ≤ U.card := le_trans (Nat.le_add_left t t) hsum

  obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq htU

  have hcard_sdiff : (U \ A).card = U.card - A.card := by
    have h' : (U \ A).card = U.card - (A ∩ U).card := by
      simpa using (Finset.card_sdiff (s := A) (t := U))
    simpa [Finset.inter_eq_left.2 hA_sub] using h'

  have htUdiff : t ≤ (U \ A).card := by
    have ht : t ≤ U.card - t :=
      (Nat.le_sub_iff_add_le htU).2 hsum
    simpa [hcard_sdiff, hA_card] using ht

  obtain ⟨B, hB_sub, hB_card⟩ := Finset.exists_subset_card_eq htUdiff

  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro x hxA hxB
    have hxBUA : x ∈ U \ A := hB_sub hxB
    exact (Finset.mem_sdiff.1 hxBUA).2 hxA

  exact ⟨A, B, hdisj, hA_card, hB_card⟩
