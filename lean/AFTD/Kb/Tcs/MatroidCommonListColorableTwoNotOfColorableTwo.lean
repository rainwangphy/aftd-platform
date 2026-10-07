import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable
import AFTD.Kb.Tcs.ThreeK4Matroid
import AFTD.Kb.Tcs.ThreeK4PartitionMatroid
import AFTD.Kb.Tcs.K4CycleMatroidIndep
import AFTD.Kb.Tcs.K4TwoForests
import AFTD.Kb.Tcs.ThreeK4PartitionMatroidIndep
import AFTD.Kb.Tcs.K4CycleMatroid
import AFTD.Kb.Tcs.K4Forest
import AFTD.Kb.Tcs.ThreeK4PartitionClass

/-!
# matroid_common_list_colorable_two_not_of_colorable_two

Topic: combinatorics   Node: b5ab3daa0612

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Theorem 1.1 (the lower bound χ_ℓ ≥ 3 and χ = 2; the upper bound χ_ℓ ≤ 3, which the paper derives from a reduction theorem and the list edge-coloring theorem for bipartite multigraphs, is not formalized); proof follows the paper's case analysis

There are two loopless matroids M₁, M₂ on a common finite ground set (M₁ graphic: three disjoint copies of K₄; M₂ a unit-capacity partition matroid with classes of size 2) that have a common coloring with two colors but are not 2-list-colorable. Hence χ_ℓ(M₁, M₂) ≠ χ(M₁, M₂) in general, refuting the conjectured equality, and the constant C of the additive-gap question is at least 1.
-/

set_option maxHeartbeats 1000000 in
theorem matroid_common_list_colorable_two_not_of_colorable_two :
    ∃ (α : Type) (M₁ M₂ : Matroid α), M₁.Finite ∧ M₁.Loopless ∧ M₂.Loopless ∧ M₁.E = M₂.E ∧
      matroid_common_colorable M₁ M₂ 2 ∧ ¬ matroid_common_list_colorable M₁ M₂ 2 := by
  classical
  have hE1 : three_k4_matroid.E = Set.univ := by
    rw [three_k4_matroid, Matroid.sum'_ground_eq]
    ext ⟨i, x⟩
    simp [k4_cycle_matroid]
  have hE2 : three_k4_partition_matroid.E = Set.univ := by
    simp [three_k4_partition_matroid]
  have hind1 : ∀ S : Set (Fin 3 × Fin 6), three_k4_matroid.Indep S ↔
      ∀ i : Fin 3, k4_forest (Finset.univ.filter fun x => (i, x) ∈ S) := by
    intro S
    simp only [three_k4_matroid, Matroid.sum'_indep_iff]
    exact forall_congr' fun i => k4_cycle_matroid_indep _
  have indep_of : ∀ S : Set (Fin 3 × Fin 6),
      (∀ i : Fin 3, ∃ T : Finset (Fin 6), (∀ x, x ∈ T ↔ (i, x) ∈ S) ∧ k4_forest T) →
        three_k4_matroid.Indep S := by
    intro S h
    rw [hind1]
    intro i
    obtain ⟨T, hT, hf⟩ := h i
    convert hf using 1
    ext x; simp [hT]
  have forest_of : ∀ S : Set (Fin 3 × Fin 6), three_k4_matroid.Indep S →
      ∀ (i : Fin 3) (T : Finset (Fin 6)), (∀ x, x ∈ T ↔ (i, x) ∈ S) → k4_forest T := by
    intro S hS i T hT
    have := (hind1 S).1 hS i
    convert this using 1
    ext x; simp [hT]
  -- the two color classes X = {a⁺, b⁺, b⁻}, Y = {a⁻, c⁺, c⁻} in every copy
  have hX1 : three_k4_matroid.Indep {e | e.2 ∈ ({0, 2, 3} : Finset (Fin 6))} :=
    indep_of _ fun _ => ⟨{0, 2, 3}, fun x => by simp, by decide⟩
  have hY1 : three_k4_matroid.Indep {e | e.2 ∉ ({0, 2, 3} : Finset (Fin 6))} :=
    indep_of _ fun _ => ⟨{1, 4, 5}, fun x => by fin_cases x <;> simp, by decide⟩
  have hX2 : three_k4_partition_matroid.Indep {e | e.2 ∈ ({0, 2, 3} : Finset (Fin 6))} := by
    rw [three_k4_partition_matroid_indep]
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    revert a b
    decide
  have hY2 : three_k4_partition_matroid.Indep {e | e.2 ∉ ({0, 2, 3} : Finset (Fin 6))} := by
    rw [three_k4_partition_matroid_indep]
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    revert a b
    decide
  refine ⟨Fin 3 × Fin 6, three_k4_matroid, three_k4_partition_matroid, ⟨hE1 ▸ Set.toFinite _⟩,
    ?_, ?_, hE1.trans hE2.symm, ?_, ?_⟩
  · rw [Matroid.loopless_iff_forall_isNonloop]
    intro e _
    rw [← Matroid.indep_singleton]
    by_cases h : e.2 ∈ ({0, 2, 3} : Finset (Fin 6))
    · exact hX1.subset (Set.singleton_subset_iff.2 h)
    · exact hY1.subset (Set.singleton_subset_iff.2 h)
  · rw [Matroid.loopless_iff_forall_isNonloop]
    intro e _
    rw [← Matroid.indep_singleton, three_k4_partition_matroid_indep]
    exact Set.injOn_singleton _ _
  · refine ⟨fun e => if e.2 ∈ ({0, 2, 3} : Finset (Fin 6)) then 0 else 1,
      fun e _ => by dsimp only; split_ifs <;> omega, fun γ => ?_⟩
    by_cases hγ : γ = 0
    · have hsub : {e | e ∈ three_k4_matroid.E ∧
          (if e.2 ∈ ({0, 2, 3} : Finset (Fin 6)) then 0 else 1) = γ} ⊆
          {e | e.2 ∈ ({0, 2, 3} : Finset (Fin 6))} := by
        intro e ⟨_, he⟩
        by_contra h
        simp only [Set.mem_setOf_eq] at h
        rw [if_neg h] at he; omega
      exact ⟨hX1.subset hsub, hX2.subset hsub⟩
    · have hsub : {e | e ∈ three_k4_matroid.E ∧
          (if e.2 ∈ ({0, 2, 3} : Finset (Fin 6)) then 0 else 1) = γ} ⊆
          {e | e.2 ∉ ({0, 2, 3} : Finset (Fin 6))} := by
        intro e ⟨_, he⟩ h
        rw [if_pos h] at he; omega
      exact ⟨hY1.subset hsub, hY2.subset hsub⟩
  · intro h
    let p : Fin 3 → ℕ := ![1, 2, 1]
    let q : Fin 3 → ℕ := ![2, 3, 3]
    have hcard : ∀ i : Fin 3, 2 ≤ ({p i, q i} : Finset ℕ).card := by decide
    obtain ⟨c, hc, hcol⟩ := h (fun e => {p e.1, q e.1}) (fun e _ => hcard e.1)
    have hpq : ∀ e, c e = p e.1 ∨ c e = q e.1 := fun e => by
      simpa using hc e (by simp [hE1])
    -- same partition class ⇒ different colors
    have hdiff : ∀ a b, three_k4_partition_class a = three_k4_partition_class b → a ≠ b →
        c a ≠ c b := by
      intro a b hab hne hcab
      have hI := (hcol (c a)).2
      rw [three_k4_partition_matroid_indep] at hI
      exact hne (hI ⟨by simp [hE1], rfl⟩ ⟨by simp [hE1], hcab.symm⟩ hab)
    have hcopy : ∀ i : Fin 3, c (i, 2) = c (i, 3) ∧ c (i, 4) = c (i, 5) ∧ c (i, 2) ≠ c (i, 4) := by
      intro i
      have h01 : c (i, 0) ≠ c (i, 1) := hdiff _ _ (by simp [three_k4_partition_class])
        (by simp)
      have hall : ∀ x, c (i, x) = c (i, 0) ∨ c (i, x) = c (i, 1) := by
        intro x
        rcases hpq (i, x) with h | h <;> rcases hpq (i, 0) with h0 | h0 <;>
          rcases hpq (i, 1) with h1 | h1 <;> simp_all
      let g : Fin 6 → Bool := fun x => decide (c (i, x) = c (i, 0))
      have hf1 := forest_of _ (hcol (c (i, 0))).1 i (Finset.univ.filter fun x => g x = true)
        (fun x => by simp [g, hE1])
      have hf2 := forest_of _ (hcol (c (i, 1))).1 i (Finset.univ.filter fun x => g x = false)
        (fun x => by
          simp only [g, hE1, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
            Set.mem_univ, decide_eq_false_iff_not]
          exact ⟨fun h' => (hall x).resolve_left h', fun h' => by rw [h']; exact h01.symm⟩)
      obtain ⟨k1, k2, k3⟩ := k4_two_forests g hf1 hf2 (by simp [g, h01.symm])
      have hform : ∀ x, c (i, x) = if g x then c (i, 0) else c (i, 1) := by
        intro x
        by_cases h : c (i, x) = c (i, 0)
        · simp [g, h]
        · simp [g, h, (hall x).resolve_left h]
      refine ⟨by rw [hform 2, hform 3, k1], by rw [hform 4, hform 5, k2], ?_⟩
      rw [hform 2, hform 4]
      cases hg2 : g 2 <;> cases hg4 : g 4 <;> simp [hg2, hg4, h01, Ne.symm h01] at k3 ⊢
    have hb : ∀ i : Fin 3, c (i, 2) ≠ c (i + 1, 5) := fun i =>
      hdiff _ _ (by revert i; decide) (by simp)
    have hc' : ∀ i : Fin 3, c (i, 4) ≠ c (i + 1, 3) := fun i =>
      hdiff _ _ (by revert i; decide) (by simp)
    obtain ⟨k02, k04, k0⟩ := hcopy 0
    obtain ⟨k12, k14, k1⟩ := hcopy 1
    obtain ⟨k22, k24, k2⟩ := hcopy 2
    have b0 : c (0, 2) ≠ c (1, 5) := hb 0
    have b1 : c (1, 2) ≠ c (2, 5) := hb 1
    have b2 : c (2, 2) ≠ c (0, 5) := hb 2
    have c0 : c (0, 4) ≠ c (1, 3) := hc' 0
    have c1 : c (1, 4) ≠ c (2, 3) := hc' 1
    have c2 : c (2, 4) ≠ c (0, 3) := hc' 2
    have p02 : c (0, 2) = 1 ∨ c (0, 2) = 2 := hpq (0, 2)
    have p04 : c (0, 4) = 1 ∨ c (0, 4) = 2 := hpq (0, 4)
    have p12 : c (1, 2) = 2 ∨ c (1, 2) = 3 := hpq (1, 2)
    have p14 : c (1, 4) = 2 ∨ c (1, 4) = 3 := hpq (1, 4)
    have p22 : c (2, 2) = 1 ∨ c (2, 2) = 3 := hpq (2, 2)
    have p24 : c (2, 4) = 1 ∨ c (2, 4) = 3 := hpq (2, 4)
    clear hcopy hb hc' hpq hdiff hcol hc
    omega
