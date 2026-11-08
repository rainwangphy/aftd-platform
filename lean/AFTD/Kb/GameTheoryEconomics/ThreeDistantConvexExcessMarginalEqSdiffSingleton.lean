import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsThreeDistantConvex

/-!
# three_distant_convex_excess_marginal_eq_sdiff_singleton

Topic: general_equilibrium   Node: 31ab6a69394e

Provenance: formalization of a published result. Source: arXiv:2611.07572 Lemma 8

Let N be a finite player type with decidable equality, and let v : Finset N → ℝ be a 3-distant convex cooperative game. For any coalition S : Finset N and any player i ∈ S, if v S - v (S \ {i}) > v Finset.univ - v (Finset.univ \ {i}), then there exists j ∈ Finset.univ \ {i} such that S = Finset.univ \ {j}.
-/

open Finset

private lemma three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_symm
    {N : Type*} [DecidableEq N] [Fintype N] (S : Finset N) (i : N) (hi : i ∈ S) :
    symmDiff S (Finset.univ \ {i}) = insert i (Finset.univ \ S) := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_singleton, true_and, not_not]
  by_cases h : x = i
  · subst h; simp [hi]
  · simp [h]

private lemma three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_union
    {N : Type*} [DecidableEq N] [Fintype N] (S : Finset N) (i : N) (hi : i ∈ S) :
    S ∪ (Finset.univ \ {i}) = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
  by_cases h : x = i <;> simp [h, hi]

private lemma three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_inter
    {N : Type*} [DecidableEq N] [Fintype N] (S : Finset N) (i : N) :
    S ∩ (Finset.univ \ {i}) = S \ {i} := by
  ext x
  simp [Finset.mem_inter, Finset.mem_sdiff]

/-- Coalitions with excess marginal contribution in 3-distant convex games are co-singletons. -/
theorem three_distant_convex_excess_marginal_eq_sdiff_singleton
    {N : Type*} [DecidableEq N] [Fintype N] {v : Finset N → ℝ}
    (hv : is_three_distant_convex v) (S : Finset N) (i : N) (hi : i ∈ S)
    (h_excess : v S - v (S \ {i}) > v Finset.univ - v (Finset.univ \ {i})) :
    ∃ j ∈ Finset.univ \ {i}, S = Finset.univ \ {j} := by
  have hunion : S ∪ (Finset.univ \ {i}) = Finset.univ :=
    three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_union S i hi
  have hinter : S ∩ (Finset.univ \ {i}) = S \ {i} :=
    three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_inter S i
  have hsymm : symmDiff S (Finset.univ \ {i}) = insert i (Finset.univ \ S) :=
    three_distant_convex_excess_marginal_eq_sdiff_singleton_aux_symm S i hi
  have hnotmem : i ∉ Finset.univ \ S := by simp [Finset.mem_sdiff, hi]
  have hcard : (symmDiff S (Finset.univ \ {i})).card = Fintype.card N - S.card + 1 := by
    rw [hsymm, Finset.card_insert_of_notMem hnotmem, Finset.card_univ_sdiff]
  have hkey : ¬ (S.card + 2 ≤ Fintype.card N) := by
    intro hle
    have h3 : 3 ≤ (symmDiff S (Finset.univ \ {i})).card := by rw [hcard]; omega
    have h := hv S (Finset.univ \ {i}) h3
    rw [hunion, hinter] at h
    linarith
  have hSne : S ≠ Finset.univ := by
    intro h
    rw [h] at h_excess
    linarith
  have hlt : S.card < Fintype.card N := by
    have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hSne
    simpa using Finset.card_lt_card hsub
  have hScc : S.card = Fintype.card N - 1 := by omega
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcompl : (Finset.univ \ S).card = 1 := by
    rw [Finset.card_univ_sdiff, hScc]; omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨j, ?_, ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨Finset.mem_univ j, ?_⟩
    intro hji
    have hjS : j ∈ Finset.univ \ S := by rw [hj]; simp
    rw [Finset.mem_sdiff] at hjS
    exact hjS.2 (hji ▸ hi)
  · rw [← hj]
    exact (Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)).symm
