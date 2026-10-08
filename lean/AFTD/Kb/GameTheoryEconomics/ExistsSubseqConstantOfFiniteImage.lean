import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MkSubseq
import AFTD.Kb.Tcs.G

/-!
# exists_subseq_constant_of_finite_image

Topic: general_equilibrium   Node: 590f91812b65

Provenance: formalization of a published result. Source: EconCSLib, `exists_subseq_constant_of_finite_image`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

exists_subseq_constant_of_finite_image
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
set_option quotPrecheck false in
variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) in
variable {n l} in
theorem exists_subseq_constant_of_finite_image {s : Finset X} (e : ℕ → X) (he : ∀ n, e n ∈ s ) :
  ∃ a ∈ s, ∃ g : ℕ ↪o ℕ,  (∀ n, e (g n) = a) := by

  have range_subset : Set.range e ⊆ (s : Set X) := Set.range_subset_iff.mpr he
  have range_finite : (Set.range e).Finite := (Finset.finite_toSet s).subset range_subset
  let imgs : Finset X := Finset.filter (fun a => ¬(Set.Finite (e ⁻¹' {a}))) s
  have imgs_nonempty : imgs.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    have preimages_all_finite : ∀ a ∈ s, Set.Finite (e ⁻¹' {a}) := by
      intro a ha
      by_contra hnf
      have a_in_imgs : a ∈ imgs := by
        simp [imgs, ha]
        exact hnf
      have : imgs ≠ ∅ := Finset.ne_empty_of_mem a_in_imgs
      contradiction
    have nat_finite : Set.Finite (Set.univ : Set ℕ) := by
      have univ_eq : Set.univ = e ⁻¹' (s : Set X) := by ext n; simp [he]
      rw [univ_eq]
      have : e ⁻¹' (s : Set X) = ⋃ a ∈ s, e ⁻¹' {a} := by
        ext n; simp [ Set.mem_preimage]
      rw [this]
      exact Set.Finite.biUnion s.finite_toSet preimages_all_finite
    exact Set.infinite_univ nat_finite

  obtain ⟨a, a_in_imgs⟩ := imgs_nonempty
  have a_in_s : a ∈ s := (Finset.mem_filter.1 a_in_imgs).1
  have a_infinite_preimage : ¬Set.Finite (e ⁻¹' {a}) := (Finset.mem_filter.1 a_in_imgs).2

  use a, a_in_s
  let preimage := e ⁻¹' {a}
  have preimage_infinite : Set.Infinite preimage := a_infinite_preimage

  have h_nonempty : preimage.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty] at preimage_infinite
    exact Set.finite_empty.not_infinite preimage_infinite
  obtain ⟨m₀, hm₀⟩ := h_nonempty
  have h_exists_larger : ∀ k : ℕ, ∃ m ∈ preimage, k < m := by
    intro k
    by_contra h_not
    push Not at h_not
    have : preimage ⊆ {n | n ≤ k} := fun n hn => h_not n hn
    have h_finite : Set.Finite preimage := (Set.finite_le_nat k).subset this
    exact preimage_infinite h_finite
  choose f hf using h_exists_larger
  have f_lt : ∀ n : ℕ, n < f n := fun n => (hf n).2
  have f_in : ∀ n : ℕ, f n ∈ preimage := fun n => (hf n).1
  let g := mk_subseq f f_lt
  have hg_in : ∀ n, g n ∈ preimage := by
    intro n
    induction' n with n ih
    · simp [g, mk_subseq]; exact f_in 0
    · simp [g, mk_subseq]; exact f_in (g n)
  have hg_strict : StrictMono g := by
    intro m n hmn
    induction' hmn with n hmn ih
    · simp [g, mk_subseq]
      exact f_lt (g m)
    · simp [g, mk_subseq]
      exact lt_trans ih (f_lt (g n))
  use OrderEmbedding.ofStrictMono g hg_strict
  intro n
  exact hg_in n
