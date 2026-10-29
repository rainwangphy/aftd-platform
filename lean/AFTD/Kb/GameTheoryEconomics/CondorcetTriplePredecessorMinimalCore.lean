import AFTD.Prelude

/-!
# condorcet_triple_predecessor_minimal_core

Topic: social_choice   Node: 62ca56bad9af

Provenance: helper lemma. IN-357 supporting structural reduction for OP-19 and the proved condorcet_dimension_le_three_iff_acyclic_weight_separation. Ordinary finite minimal-counterexample argument, with no novelty claim. The2015 high-girth S3 construction (Theorem11, https://drops.dagstuhl.de/storage/00lipics/lipics-vol040-approx-random2015/LIPIcs.APPROX-RANDOM.2015.78/LIPIcs.APPROX-RANDOM.2015.78.pdf) prevents assuming bounded-size cores; no such bound is asserted.

For every finite directed relation with an outside common predecessor for every vertex set of size at most three, there is an induced subset A of at least four vertices retaining this property and having minimum cardinality among ALL induced subsets retaining it. This is a global minimum, stronger than vertex-deletion criticality alone. For every vertex a in A there is a set J contained in A, of size exactly three and excluding a, such that a points to all of J and is the unique outside common predecessor of J within A. The statement does not bound the size of A.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_triple_predecessor_minimal_core
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) :
    ∃ A : Finset (Fin m), 4 ≤ A.card ∧
      (∀ J : Finset (Fin m), J ⊆ A → J.card ≤ 3 →
        ∃ a, a ∈ A ∧ a ∉ J ∧ ∀ b ∈ J, R a b) ∧
      (∀ B : Finset (Fin m),
        (∀ J : Finset (Fin m), J ⊆ B → J.card ≤ 3 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, R a b) → A.card ≤ B.card) ∧
      (∀ a ∈ A, ∃ J : Finset (Fin m), J ⊆ A ∧ J.card = 3 ∧ a ∉ J ∧
        (∀ b ∈ J, R a b) ∧
        ∀ c, c ∈ A → c ∉ J → (∀ b ∈ J, R c b) → c = a) := by
  classical
  let P : Finset (Fin m) → Prop := fun A =>
    ∀ J : Finset (Fin m), J ⊆ A → J.card ≤ 3 →
      ∃ a, a ∈ A ∧ a ∉ J ∧ ∀ b ∈ J, R a b
  let F : Finset (Finset (Fin m)) := univ.filter P
  have hF : (univ : Finset (Fin m)) ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro J hJ hcard
    obtain ⟨a, ha, hR⟩ := hroot J hcard
    exact ⟨a, mem_univ _, ha, hR⟩
  obtain ⟨A, hAF, hmin⟩ := F.exists_min_image Finset.card ⟨univ, hF⟩
  have hA : P A := (mem_filter.mp hAF).2
  have hfour : 4 ≤ A.card := by
    by_contra h
    have hcard : A.card ≤ 3 := by omega
    obtain ⟨a, ha, hna, _⟩ := hA A (subset_refl A) hcard
    exact hna ha
  refine ⟨A, hfour, hA,
    fun B hB => hmin B (mem_filter.mpr ⟨mem_univ _, hB⟩), ?_⟩
  intro a ha
  have hdelete : ¬ P (A.erase a) := by
    intro hP
    have hle := hmin (A.erase a) (mem_filter.mpr ⟨mem_univ _, hP⟩)
    have hdrop := card_erase_lt_of_mem ha
    omega
  have hbad : ∃ J : Finset (Fin m), J ⊆ A.erase a ∧ J.card ≤ 3 ∧
      ¬ ∃ c, c ∈ A.erase a ∧ c ∉ J ∧ ∀ b ∈ J, R c b := by
    by_contra hnone
    apply hdelete
    intro J hsub hcard
    by_contra hNo
    exact hnone ⟨J, hsub, hcard, hNo⟩
  obtain ⟨J, hJsub, hJcard, hJnone⟩ := hbad
  have hJA : J ⊆ A := hJsub.trans (erase_subset a A)
  have hprivate : ∀ c, c ∈ A → c ∉ J → (∀ b ∈ J, R c b) → c = a := by
    intro c hc hcJ hcR
    by_contra hne
    exact hJnone ⟨c, mem_erase.mpr ⟨hne, hc⟩, hcJ, hcR⟩
  obtain ⟨c, hc, hcJ, hcR⟩ := hA J hJA hJcard
  have heq := hprivate c hc hcJ hcR
  subst c
  have hJthree : J.card = 3 := by
    by_contra hne
    have hJtwo : J.card ≤ 2 := by omega
    have hsub : insert a J ⊆ A := insert_subset ha hJA
    have hcard : (insert a J).card ≤ 3 := by
      rw [card_insert_of_notMem hcJ]
      omega
    obtain ⟨r, hrA, hrnot, hrR⟩ := hA (insert a J) hsub hcard
    have hrJ : r ∉ J := fun hr => hrnot (mem_insert_of_mem hr)
    have hra : r = a := hprivate r hrA hrJ
      (fun b hb => hrR b (mem_insert_of_mem hb))
    subst r
    exact hrnot (mem_insert_self a J)
  exact ⟨J, hJA, hJthree, hcJ, hcR, hprivate⟩
