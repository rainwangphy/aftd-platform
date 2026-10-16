import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.CodeDist
import AFTD.Kb.Tcs.CodeDistEqZeroOfCodeKEqZero
import AFTD.Kb.Tcs.CodeDistLeN
import AFTD.Kb.Tcs.CodeK
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.DistImpliesCorrectable
import AFTD.Kb.Tcs.ExistsDisjointFinsetsCard
import AFTD.Kb.Tcs.TwoDisjointCorrectableSetsBoundLogicalDimension
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.Tcs.VSubUnivEqTop

/-!
# quantum_singleton_bound

Topic: quantum   Node: 396d60a285a2

Provenance: formalization of a published result. Source: Quantum Singleton bound, as formalized in TCSlib (`quantum_singleton_bound`). Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Let $p$ be prime and work in the symplectic space $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$
equipped with the form $\omega$. If $S \le V$ is an isotropic subspace, so that
$\omega(u,v) = 0$ for all $u, v \in S$, then its logical dimension $k(S) = n - \dim(S)$
and its distance $d(S)$ satisfy
\[
k(S) + 2\bigl(d(S) - 1\bigr) \;\le\; n .
\]
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
/-- Quantum Singleton bound: `code_k S + 2*(code_dist S - 1) ≤ n`. -/
theorem quantum_singleton_bound
    (S : Submodule (F p) (V n p))
    (hS : IsIsotropic (n:=n) (p:=p) S) :
    code_k (n:=n) (p:=p) S + 2 * (code_dist (n:=n) (p:=p) S - 1) ≤ n := by
  classical

  -- Case split on `code_dist S`.
  cases hcd : code_dist (n:=n) (p:=p) S with
  | zero =>
      have hk_le : code_k (n:=n) (p:=p) S ≤ n := by
        simpa [code_k] using (Nat.sub_le n (Module.finrank (F p) S))
      simpa [hcd] using hk_le

  | succ d' =>
      have hd_pred : code_dist (n:=n) (p:=p) S - 1 = d' := by
        simpa [hcd] using (Nat.succ_sub_one d')

      have hd'_lt : d' < code_dist (n:=n) (p:=p) S := by
        simpa [hcd] using (Nat.lt_succ_self d')

      have h2t : 2 * d' ≤ n := by
        by_contra hnot
        have hn : n < 2 * d' := Nat.lt_of_not_ge hnot

        have hd_le_n : code_dist (n:=n) (p:=p) S ≤ n :=
          code_dist_le_n (n:=n) (p:=p) S
        have hsucc_le : Nat.succ d' ≤ n := by simpa [hcd] using hd_le_n
        have hd'_le_n : d' ≤ n := Nat.le_of_lt (Nat.lt_of_succ_le hsucc_le)

        have hdU : d' ≤ (Finset.univ : Finset (Fin n)).card := by
          simpa [Finset.card_univ] using hd'_le_n
        obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq hdU

        let B : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ A

        have hdisj : Disjoint A B := by
          refine Finset.disjoint_left.2 ?_
          intro x hxA hxB
          have hxBUA : x ∈ (Finset.univ : Finset (Fin n)) \ A := by simpa [B] using hxB
          exact (Finset.mem_sdiff.1 hxBUA).2 hxA

        -- Compute `B.card = n - d'`.
        have hB_card : B.card = n - d' := by
          have h' :
              ((Finset.univ : Finset (Fin n)) \ A).card
                =
              (Finset.univ : Finset (Fin n)).card - (A ∩ (Finset.univ : Finset (Fin n))).card := by
            simpa using (Finset.card_sdiff (s := A) (t := (Finset.univ : Finset (Fin n))))
          simpa [B, hA_card, Finset.card_univ, Finset.inter_eq_left.2 hA_sub] using h'

        have hA_corr : correctable (n:=n) (p:=p) S A := by
          apply dist_implies_correctable (n:=n) (p:=p) S A
          simpa [hA_card] using hd'_lt

        have hB_corr : correctable (n:=n) (p:=p) S B := by
          apply dist_implies_correctable (n:=n) (p:=p) S B
          have hle : n - d' ≤ d' := by
            apply (Nat.sub_le_iff_le_add).2
            exact Nat.le_of_lt (by simpa [two_mul] using hn)
          have hlt : n - d' < Nat.succ d' := Nat.lt_succ_of_le hle
          simpa [hB_card, hcd] using hlt

        have hk_le :
            code_k (n:=n) (p:=p) S
              ≤ ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card :=
          two_disjoint_correctable_sets_bound_logical_dimension
            (n:=n) (p:=p) S hS A B hdisj hA_corr hB_corr

        have hAU : A ∪ B = (Finset.univ : Finset (Fin n)) := by
          ext x
          simp [B]

        have hcomp0 : ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card = 0 := by
          simpa [hAU]

        have hk_le0 : code_k (n:=n) (p:=p) S ≤ 0 := by
          simpa [hcomp0] using hk_le

        have hk0 : code_k (n:=n) (p:=p) S = 0 :=
          Nat.eq_zero_of_le_zero hk_le0

        have hd0 : code_dist (n:=n) (p:=p) S = 0 :=
          code_dist_eq_zero_of_code_k_eq_zero (n:=n) (p:=p) S hS hk0

        have : Nat.succ d' = 0 := by
          simpa [hcd] using hd0
        exact (Nat.succ_ne_zero d') this

      obtain ⟨A, B, hdisj, hA_card, hB_card⟩ :=
        exists_disjoint_finsets_card (n:=n) d' h2t

      have hA_corr : correctable (n:=n) (p:=p) S A := by
        apply dist_implies_correctable (n:=n) (p:=p) S A
        simpa [hA_card] using hd'_lt

      have hB_corr : correctable (n:=n) (p:=p) S B := by
        apply dist_implies_correctable (n:=n) (p:=p) S B
        simpa [hB_card] using hd'_lt

      have hk_leC :
          code_k (n:=n) (p:=p) S
            ≤ ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card :=
        two_disjoint_correctable_sets_bound_logical_dimension
          (n:=n) (p:=p) S hS A B hdisj hA_corr hB_corr

      have hC :
          ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card = n - 2 * d' := by
        have hsdiff :
            ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - ((A ∪ B) ∩ (Finset.univ : Finset (Fin n))).card := by
          simpa using
            (Finset.card_sdiff (s := (A ∪ B)) (t := (Finset.univ : Finset (Fin n))))
        have hinter :
            ((A ∪ B) ∩ (Finset.univ : Finset (Fin n))) = (A ∪ B) :=
          Finset.inter_eq_left.2 (Finset.subset_univ _)
        have hsdiff' :
            ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - (A ∪ B).card := by
          simpa [hinter] using hsdiff
        have hunion : (A ∪ B).card = 2 * d' := by
          calc
            (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
            _ = d' + d' := by simp [hA_card, hB_card]
            _ = 2 * d' := by simpa [two_mul]
        calc
          ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - (A ∪ B).card := hsdiff'
          _ = n - 2 * d' := by simp [Finset.card_univ, hunion]

      have hk_le_sub : code_k (n:=n) (p:=p) S ≤ n - 2 * d' := by
        simpa [hC] using hk_leC

      have hmain : code_k (n:=n) (p:=p) S + 2 * d' ≤ n := by
        calc
          code_k (n:=n) (p:=p) S + 2 * d'
              ≤ (n - 2 * d') + 2 * d' := by
                  exact Nat.add_le_add_right hk_le_sub _
          _ = n := by
                  exact Nat.sub_add_cancel h2t

      simpa [hd_pred] using hmain
