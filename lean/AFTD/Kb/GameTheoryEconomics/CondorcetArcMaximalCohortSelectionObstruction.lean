import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_arc_maximal_cohort_selection_obstruction

Topic: social_choice   Node: 8bac11ac97cd

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

There is an eleven-vertex S2 relation with six acyclic sets, exactly three memberships per vertex, and a rank-compatible description with injective rankings. It is arc-maximal among relations preserving those six acyclic restrictions, and its only induced S2 subset is the full set. Two distinct vertices have the same activity signature. It explicitly fails S3. Thus even arc saturation and induced minimality do not justify one representative per activity type from S2 half-cover assumptions. This is not a counterexample to the main election conjecture or to an S3-specific reduction.
-/

open Finset
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
def condorcet_maximal_cohort_gap_sets : Fin 6 → Finset (Fin 11) := ![{0,1,2,3,5,6,7},{0,1,4,5,6,8},{0,2,3,4,9},{1,2,3,4,10},{5,7,8,9,10},{6,7,8,9,10}]
def condorcet_maximal_cohort_gap_rank : Fin 6 → Fin 11 → ℕ := ![![6,5,1,4,15,3,2,0,19,20,21],![4,3,13,14,5,1,0,18,2,20,21],![0,12,4,2,1,16,17,18,19,3,21],![11,3,1,2,0,16,17,18,19,20,4],![11,12,13,14,15,2,17,4,3,1,0],![11,12,13,14,15,16,4,3,2,1,0]]
def condorcet_maximal_cohort_gap_pred : Fin 11 → ℕ := ![1506,1004,912,496,481,1604,1668,1808,1580,1051,31]
def condorcet_maximal_cohort_gap_relation (a b : Fin 11) : Prop :=
  (condorcet_maximal_cohort_gap_pred b).testBit a.val = true
instance : DecidableRel condorcet_maximal_cohort_gap_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_maximal_cohort_gap_pred b).testBit a.val = true))

theorem condorcet_maximal_cohort_gap_rank_exact : ∀ a b : Fin 11,
    condorcet_maximal_cohort_gap_relation a b ↔ a ≠ b ∧
      ∀ v, a ∈ condorcet_maximal_cohort_gap_sets v → b ∈ condorcet_maximal_cohort_gap_sets v →
        condorcet_maximal_cohort_gap_rank v a < condorcet_maximal_cohort_gap_rank v b := by decide

theorem condorcet_maximal_cohort_gap_pair_check :
    (∀ a : Fin 11, ¬condorcet_maximal_cohort_gap_relation a a) ∧
    (∀ a b : Fin 11, ∃ c, condorcet_maximal_cohort_gap_relation c a ∧
      condorcet_maximal_cohort_gap_relation c b) := by decide

set_option synthInstance.maxSize 10000 in
theorem condorcet_maximal_cohort_gap_boolean_closure :
    ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Bool,
      ((x0 = true) ∨ (x1 = true) ∨ (x2 = true) ∨ (x3 = true) ∨ (x4 = true) ∨ (x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true) ∨ (x9 = true) ∨ (x10 = true)) →
      ((x0 = true) → (x0 = true) → ((x1 = true) ∨ (x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true) ∨ (x10 = true))) →
      ((x0 = true) → (x10 = true) → ((x1 = true))) →
      ((x1 = true) → (x1 = true) → ((x2 = true) ∨ (x3 = true) ∨ (x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true) ∨ (x9 = true))) →
      ((x1 = true) → (x9 = true) → ((x3 = true))) →
      ((x2 = true) → (x2 = true) → ((x4 = true) ∨ (x7 = true) ∨ (x8 = true) ∨ (x9 = true))) →
      ((x2 = true) → (x4 = true) → ((x7 = true) ∨ (x8 = true))) →
      ((x2 = true) → (x8 = true) → ((x9 = true))) →
      ((x3 = true) → (x3 = true) → ((x4 = true) ∨ (x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true))) →
      ((x3 = true) → (x4 = true) → ((x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true))) →
      ((x3 = true) → (x8 = true) → ((x5 = true))) →
      ((x3 = true) → (x10 = true) → ((x4 = true))) →
      ((x4 = true) → (x4 = true) → ((x0 = true) ∨ (x5 = true) ∨ (x6 = true) ∨ (x7 = true) ∨ (x8 = true))) →
      ((x4 = true) → (x5 = true) → ((x6 = true))) →
      ((x4 = true) → (x6 = true) → ((x7 = true))) →
      ((x4 = true) → (x7 = true) → ((x8 = true))) →
      ((x4 = true) → (x10 = true) → ((x0 = true))) →
      ((x5 = true) → (x5 = true) → ((x2 = true) ∨ (x6 = true) ∨ (x9 = true) ∨ (x10 = true))) →
      ((x5 = true) → (x9 = true) → ((x10 = true))) →
      ((x5 = true) → (x10 = true) → ((x2 = true))) →
      ((x6 = true) → (x6 = true) → ((x2 = true) ∨ (x7 = true) ∨ (x9 = true) ∨ (x10 = true))) →
      ((x6 = true) → (x9 = true) → ((x10 = true))) →
      ((x6 = true) → (x10 = true) → ((x2 = true))) →
      ((x7 = true) → (x7 = true) → ((x4 = true) ∨ (x8 = true) ∨ (x9 = true) ∨ (x10 = true))) →
      ((x7 = true) → (x8 = true) → ((x9 = true) ∨ (x10 = true))) →
      ((x7 = true) → (x9 = true) → ((x4 = true) ∨ (x10 = true))) →
      ((x7 = true) → (x10 = true) → ((x4 = true))) →
      ((x8 = true) → (x8 = true) → ((x2 = true) ∨ (x3 = true) ∨ (x5 = true) ∨ (x9 = true) ∨ (x10 = true))) →
      ((x8 = true) → (x9 = true) → ((x3 = true) ∨ (x10 = true))) →
      ((x8 = true) → (x10 = true) → ((x2 = true) ∨ (x3 = true))) →
      ((x9 = true) → (x9 = true) → ((x0 = true) ∨ (x1 = true) ∨ (x3 = true) ∨ (x4 = true) ∨ (x10 = true))) →
      ((x9 = true) → (x10 = true) → ((x0 = true) ∨ (x1 = true) ∨ (x3 = true) ∨ (x4 = true))) →
      ((x10 = true) → (x10 = true) → ((x0 = true) ∨ (x1 = true) ∨ (x2 = true) ∨ (x3 = true) ∨ (x4 = true))) →
      (x0 = true) ∧ (x1 = true) ∧ (x2 = true) ∧ (x3 = true) ∧ (x4 = true) ∧ (x5 = true) ∧ (x6 = true) ∧ (x7 = true) ∧ (x8 = true) ∧ (x9 = true) ∧ (x10 = true) := by decide

theorem condorcet_maximal_cohort_gap_minimum_check : ∀ B : Finset (Fin 11),
    B.Nonempty →
    (∀ a ∈ B, ∃ b ∈ B, condorcet_maximal_cohort_gap_relation b a) →
    (∀ a ∈ B, ∀ b ∈ B, ∃ c ∈ B,
      condorcet_maximal_cohort_gap_relation c a ∧ condorcet_maximal_cohort_gap_relation c b) →
    B = univ := by
  classical
  intro B hne _ hpair
  have hnon : (0 ∈ B) ∨ (1 ∈ B) ∨ (2 ∈ B) ∨ (3 ∈ B) ∨ (4 ∈ B) ∨ (5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B) ∨ (9 ∈ B) ∨ (10 ∈ B) := by
    obtain ⟨a,ha⟩ := hne
    fin_cases a
    · exact (Or.inl ha)
    · exact (Or.inr (Or.inl ha))
    · exact (Or.inr (Or.inr (Or.inl ha)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))))))))
  have h0 : (0 ∈ B) → (0 ∈ B) → ((1 ∈ B) ∨ (5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 0 ha 0 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 0 →
        condorcet_maximal_cohort_gap_relation z 0 → (z = 1 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
  have h1 : (0 ∈ B) → (10 ∈ B) → ((1 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 0 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 0 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 1) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h2 : (1 ∈ B) → (1 ∈ B) → ((2 ∈ B) ∨ (3 ∈ B) ∨ (5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B) ∨ (9 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 1 ha 1 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 1 →
        condorcet_maximal_cohort_gap_relation z 1 → (z = 2 ∨ z = 3 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))
  have h3 : (1 ∈ B) → (9 ∈ B) → ((3 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 1 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 1 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 3) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h4 : (2 ∈ B) → (2 ∈ B) → ((4 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B) ∨ (9 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 2 ha 2 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 2 →
        condorcet_maximal_cohort_gap_relation z 2 → (z = 4 ∨ z = 7 ∨ z = 8 ∨ z = 9) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h5 : (2 ∈ B) → (4 ∈ B) → ((7 ∈ B) ∨ (8 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 2 ha 4 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 2 →
        condorcet_maximal_cohort_gap_relation z 4 → (z = 7 ∨ z = 8) := by decide
    rcases hr c hca hcb with rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr hc)
  have h6 : (2 ∈ B) → (8 ∈ B) → ((9 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 2 ha 8 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 2 →
        condorcet_maximal_cohort_gap_relation z 8 → (z = 9) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h7 : (3 ∈ B) → (3 ∈ B) → ((4 ∈ B) ∨ (5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 3 ha 3 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 3 →
        condorcet_maximal_cohort_gap_relation z 3 → (z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have h8 : (3 ∈ B) → (4 ∈ B) → ((5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 3 ha 4 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 3 →
        condorcet_maximal_cohort_gap_relation z 4 → (z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h9 : (3 ∈ B) → (8 ∈ B) → ((5 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 3 ha 8 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 3 →
        condorcet_maximal_cohort_gap_relation z 8 → (z = 5) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h10 : (3 ∈ B) → (10 ∈ B) → ((4 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 3 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 3 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 4) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h11 : (4 ∈ B) → (4 ∈ B) → ((0 ∈ B) ∨ (5 ∈ B) ∨ (6 ∈ B) ∨ (7 ∈ B) ∨ (8 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 4 ha 4 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 4 →
        condorcet_maximal_cohort_gap_relation z 4 → (z = 0 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have h12 : (4 ∈ B) → (5 ∈ B) → ((6 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 4 ha 5 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 4 →
        condorcet_maximal_cohort_gap_relation z 5 → (z = 6) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h13 : (4 ∈ B) → (6 ∈ B) → ((7 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 4 ha 6 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 4 →
        condorcet_maximal_cohort_gap_relation z 6 → (z = 7) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h14 : (4 ∈ B) → (7 ∈ B) → ((8 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 4 ha 7 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 4 →
        condorcet_maximal_cohort_gap_relation z 7 → (z = 8) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h15 : (4 ∈ B) → (10 ∈ B) → ((0 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 4 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 4 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 0) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h16 : (5 ∈ B) → (5 ∈ B) → ((2 ∈ B) ∨ (6 ∈ B) ∨ (9 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 5 ha 5 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 5 →
        condorcet_maximal_cohort_gap_relation z 5 → (z = 2 ∨ z = 6 ∨ z = 9 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h17 : (5 ∈ B) → (9 ∈ B) → ((10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 5 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 5 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 10) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h18 : (5 ∈ B) → (10 ∈ B) → ((2 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 5 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 5 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 2) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h19 : (6 ∈ B) → (6 ∈ B) → ((2 ∈ B) ∨ (7 ∈ B) ∨ (9 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 6 ha 6 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 6 →
        condorcet_maximal_cohort_gap_relation z 6 → (z = 2 ∨ z = 7 ∨ z = 9 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h20 : (6 ∈ B) → (9 ∈ B) → ((10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 6 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 6 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 10) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h21 : (6 ∈ B) → (10 ∈ B) → ((2 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 6 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 6 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 2) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h22 : (7 ∈ B) → (7 ∈ B) → ((4 ∈ B) ∨ (8 ∈ B) ∨ (9 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 7 ha 7 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 7 →
        condorcet_maximal_cohort_gap_relation z 7 → (z = 4 ∨ z = 8 ∨ z = 9 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h23 : (7 ∈ B) → (8 ∈ B) → ((9 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 7 ha 8 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 7 →
        condorcet_maximal_cohort_gap_relation z 8 → (z = 9 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr hc)
  have h24 : (7 ∈ B) → (9 ∈ B) → ((4 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 7 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 7 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 4 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr hc)
  have h25 : (7 ∈ B) → (10 ∈ B) → ((4 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 7 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 7 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 4) := by decide
    have heq := hr c hca hcb
    subst c
    exact hc
  have h26 : (8 ∈ B) → (8 ∈ B) → ((2 ∈ B) ∨ (3 ∈ B) ∨ (5 ∈ B) ∨ (9 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 8 ha 8 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 8 →
        condorcet_maximal_cohort_gap_relation z 8 → (z = 2 ∨ z = 3 ∨ z = 5 ∨ z = 9 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have h27 : (8 ∈ B) → (9 ∈ B) → ((3 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 8 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 8 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 3 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr hc)
  have h28 : (8 ∈ B) → (10 ∈ B) → ((2 ∈ B) ∨ (3 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 8 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 8 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 2 ∨ z = 3) := by decide
    rcases hr c hca hcb with rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr hc)
  have h29 : (9 ∈ B) → (9 ∈ B) → ((0 ∈ B) ∨ (1 ∈ B) ∨ (3 ∈ B) ∨ (4 ∈ B) ∨ (10 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 9 ha 9 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 9 →
        condorcet_maximal_cohort_gap_relation z 9 → (z = 0 ∨ z = 1 ∨ z = 3 ∨ z = 4 ∨ z = 10) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have h30 : (9 ∈ B) → (10 ∈ B) → ((0 ∈ B) ∨ (1 ∈ B) ∨ (3 ∈ B) ∨ (4 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 9 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 9 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 0 ∨ z = 1 ∨ z = 3 ∨ z = 4) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr hc)))
  have h31 : (10 ∈ B) → (10 ∈ B) → ((0 ∈ B) ∨ (1 ∈ B) ∨ (2 ∈ B) ∨ (3 ∈ B) ∨ (4 ∈ B)) := by
    intro ha hb
    obtain ⟨c,hc,hca,hcb⟩ := hpair 10 ha 10 hb
    have hr : ∀ z : Fin 11, condorcet_maximal_cohort_gap_relation z 10 →
        condorcet_maximal_cohort_gap_relation z 10 → (z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4) := by decide
    rcases hr c hca hcb with rfl | rfl | rfl | rfl | rfl
    · exact (Or.inl hc)
    · exact (Or.inr (Or.inl hc))
    · exact (Or.inr (Or.inr (Or.inl hc)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have hlogic := condorcet_maximal_cohort_gap_boolean_closure (decide (0 ∈ B)) (decide (1 ∈ B)) (decide (2 ∈ B)) (decide (3 ∈ B)) (decide (4 ∈ B)) (decide (5 ∈ B)) (decide (6 ∈ B)) (decide (7 ∈ B)) (decide (8 ∈ B)) (decide (9 ∈ B)) (decide (10 ∈ B))
  simp only [decide_eq_true_eq] at hlogic
  have hfull := hlogic hnon h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  rcases hfull with ⟨hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8,hf9,hf10⟩
  apply eq_univ_of_forall
  intro a
  fin_cases a
  · exact hf0
  · exact hf1
  · exact hf2
  · exact hf3
  · exact hf4
  · exact hf5
  · exact hf6
  · exact hf7
  · exact hf8
  · exact hf9
  · exact hf10

theorem condorcet_maximal_cohort_gap_reverse_check : ∀ a b : Fin 11,
    a ≠ b → ¬condorcet_maximal_cohort_gap_relation a b →
    ∃ v : Fin 6, a ∈ condorcet_maximal_cohort_gap_sets v ∧
      b ∈ condorcet_maximal_cohort_gap_sets v ∧
      (condorcet_maximal_cohort_gap_relation b a ∨
        ∃ c : Fin 11, c ∈ condorcet_maximal_cohort_gap_sets v ∧
          condorcet_maximal_cohort_gap_relation b c ∧
          condorcet_maximal_cohort_gap_relation c a) := by decide

theorem condorcet_arc_maximal_cohort_selection_obstruction :
    ∃ (R : Fin 11 → Fin 11 → Prop) (U : Fin 6 → Finset (Fin 11))
      (p : Fin 6 → Fin 11 → ℕ),
      (∀ a b, R a b ↔ a ≠ b ∧ ∀ v, a ∈ U v → b ∈ U v → p v a < p v b) ∧
      (∀ v, Function.Injective (p v)) ∧
      (∀ J : Finset (Fin 11), J.card ≤ 2 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin 11 // a ∈ U v} => R a.val b.val)) ∧
      (∀ a, (univ.filter fun v => a ∈ U v).card = 3) ∧
      (∀ Q : Fin 11 → Fin 11 → Prop,
        (∀ a b, R a b → Q a b) →
        (∀ v, WellFounded (fun a b : {a : Fin 11 // a ∈ U v} => Q a.val b.val)) →
        ∀ a b, Q a b → R a b) ∧
      (∀ B : Finset (Fin 11),
        (∀ J : Finset (Fin 11), J ⊆ B → J.card ≤ 2 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, R a b) → B = univ) ∧
      (∃ a b : Fin 11, a ≠ b ∧ ∀ v, a ∈ U v ↔ b ∈ U v) ∧
      ¬(∀ J : Finset (Fin 11), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) := by
  let R := condorcet_maximal_cohort_gap_relation
  let U := condorcet_maximal_cohort_gap_sets
  let p := condorcet_maximal_cohort_gap_rank
  have hloop : ∀ a, ¬R a a := condorcet_maximal_cohort_gap_pair_check.1
  have hpair : ∀ a b, ∃ c, R c a ∧ R c b := condorcet_maximal_cohort_gap_pair_check.2
  have hroot : ∀ J : Finset (Fin 11), J.card ≤ 2 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b := by
    intro J hJ
    by_cases h0 : J.card = 0
    · have hJ0 : J = ∅ := card_eq_zero.mp h0
      subst J
      exact ⟨0,by simp,by simp⟩
    · by_cases h1 : J.card = 1
      · obtain ⟨a,rfl⟩ := card_eq_one.mp h1
        obtain ⟨c,hca,_⟩ := hpair a a
        refine ⟨c,?_,?_⟩
        · simpa only [mem_singleton] using (fun heq : c = a => hloop a (heq ▸ hca))
        · intro b hb
          have heq : b = a := mem_singleton.mp hb
          subst b
          exact hca
      · have h2 : J.card = 2 := by omega
        obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp h2
        obtain ⟨c,hca,hcb⟩ := hpair a b
        refine ⟨c,?_,?_⟩
        · simp only [mem_insert,mem_singleton,not_or]
          exact ⟨fun heq => hloop a (heq ▸ hca),fun heq => hloop b (heq ▸ hcb)⟩
        · intro d hd
          simp only [mem_insert,mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hca
          · exact hcb
  have hU : ∀ v, WellFounded (fun a b : {a : Fin 11 // a ∈ U v} => R a.val b.val) := by
    intro v
    refine (measure (fun a : {a : Fin 11 // a ∈ U v} => p v a.val)).wf.mono ?_
    intro a b hab
    exact ((condorcet_maximal_cohort_gap_rank_exact a b).mp hab).2 v a.property b.property
  refine ⟨R,U,p,condorcet_maximal_cohort_gap_rank_exact,?_,hroot,hU,?_,?_,?_,?_,?_⟩
  · decide
  · decide
  · intro Q hRQ hQU a b hab
    by_contra hnot
    by_cases heq : a = b
    · subst b
      have hactive : ∀ a : Fin 11, ∃ v : Fin 6, a ∈ U v := by decide
      obtain ⟨v,hv⟩ := hactive a
      exact (hQU v).asymmetric ⟨a,hv⟩ ⟨a,hv⟩ hab hab
    · obtain ⟨v,hav,hbv,hrev⟩ := condorcet_maximal_cohort_gap_reverse_check a b heq hnot
      rcases hrev with hba | ⟨c,hcv,hbc,hca⟩
      · exact (hQU v).asymmetric ⟨a,hav⟩ ⟨b,hbv⟩ hab (hRQ b a hba)
      · exact (hQU v).asymmetric₃ ⟨a,hav⟩ ⟨b,hbv⟩ ⟨c,hcv⟩ hab
          (hRQ b c hbc) (hRQ c a hca)
  · intro B hB
    apply condorcet_maximal_cohort_gap_minimum_check B
    · obtain ⟨a,ha,_,_⟩ := hB ∅ (by simp) (by simp)
      exact ⟨a,ha⟩
    · intro a ha
      obtain ⟨b,hb,_,hba⟩ := hB {a} (singleton_subset_iff.mpr ha) (by simp)
      exact ⟨b,hb,hba a (by simp)⟩
    · intro a ha b hb
      obtain ⟨c,hc,_,hcr⟩ := hB {a,b} (insert_subset ha (singleton_subset_iff.mpr hb))
        ((card_insert_le _ _).trans (by simp))
      exact ⟨c,hc,hcr a (by simp),hcr b (by simp)⟩
  · exact ⟨2,3,by decide,by decide⟩
  · intro hthree
    obtain ⟨a,_,ha⟩ := hthree {0,1,9} (by decide)
    have hbad : ∀ a : Fin 11, ¬(R a 0 ∧ R a 1 ∧ R a 9) := by decide
    exact hbad a ⟨ha 0 (by simp),ha 1 (by simp),ha 9 (by simp)⟩
