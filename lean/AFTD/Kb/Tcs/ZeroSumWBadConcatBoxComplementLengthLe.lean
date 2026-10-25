import AFTD.Prelude
import AFTD.Kb.Tcs.IntegerBoxCompletionCardLe
import AFTD.Kb.Tcs.ZeroSumWBad
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq

/-!
# zero_sum_w_bad_concat_box_complement_length_le

Topic: combinatorics   Node: b72f56986af0

Provenance: helper lemma. Supporting lemmas for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is the restricted full-box completion route; no claim that an arbitrary long bad sequence contains such a box.

If B++A is w-bad and every vector of [0,n-1]^r is the exact sum of a subsequence of B, then the complementary list A has length at most r(n-1).
-/

theorem zero_sum_w_bad_concat_box_complement_length_le
    (n r : ℕ) (hn : 1 < n) (B A : List (Fin r → ℤ))
    (hbad : zero_sum_w_bad n (B ++ A))
    (hbox : ∀ c : Fin r → ℤ, (∀ j, 0 ≤ c j ∧ c j < n) →
      ∃ I : Finset (Fin B.length), ∀ j, ∑ i ∈ I, B.get i j = c j) :
    A.length ≤ r * (n - 1) := by
  classical
  have hgood : ∀ P : Finset (Fin (B ++ A).length),
      (∀ j, (n : ℤ) ∣ ∑ i ∈ P, (B ++ A).get i j) →
      ∀ j, (n : ℤ) ^ 2 ∣ ∑ i ∈ P, (B ++ A).get i j := by
    intro P hp j
    by_contra h
    have hne : P.Nonempty := by
      by_contra he
      have he' : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simpa [he'] using h
    exact hbad.2 P ⟨hne, hp, j, h⟩
  have hc := integer_box_completion_card_le n r hn (fun i : Fin A.length => A.get i)
    (fun i => hbad.1 (A.get i) (List.mem_append.mpr (Or.inr (List.get_mem A i))))
  simp only [Fintype.card_fin] at hc
  apply hc
  intro s c hcb hdiv j
  obtain ⟨I, hI⟩ := hbox c hcb
  let fB : Fin B.length ↪ Fin (B ++ A).length :=
    ⟨fun i => ⟨i.val, by simp only [List.length_append]; omega⟩,
      fun i k h => Fin.ext (congrArg (fun q : Fin (B ++ A).length => q.val) h)⟩
  let fA : Fin A.length ↪ Fin (B ++ A).length :=
    ⟨fun i => ⟨B.length + i.val, by simp only [List.length_append]; omega⟩,
      fun i k h => Fin.ext (by have := congrArg (fun q : Fin (B ++ A).length => q.val) h; change B.length + i.val = B.length + k.val at this; omega)⟩
  have hgetB : ∀ i, (B ++ A).get (fB i) = B.get i := by
    intro i
    change (B ++ A)[i.val] = B[i.val]
    exact List.getElem_append_left i.isLt
  have hgetA : ∀ i, (B ++ A).get (fA i) = A.get i := by
    intro i
    change (B ++ A)[B.length + i.val] = A[i.val]
    rw [List.getElem_append_right (by omega)]
    simp
  have hd : Disjoint (I.map fB) (s.map fA) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
    obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hy
    have he := congrArg Fin.val (hi.trans hk.symm)
    change i.val = B.length + k.val at he
    omega
  let P := I.map fB ∪ s.map fA
  have hsum : ∀ j, ∑ i ∈ P, (B ++ A).get i j = c j + ∑ i ∈ s, A.get i j := by
    intro j
    rw [Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
    simp only [hgetB, hgetA, hI]
  have hp : ∀ j, (n : ℤ) ∣ ∑ i ∈ P, (B ++ A).get i j := by
    intro j
    rw [hsum]
    exact hdiv j
  have h := hgood P hp j
  rwa [hsum] at h
