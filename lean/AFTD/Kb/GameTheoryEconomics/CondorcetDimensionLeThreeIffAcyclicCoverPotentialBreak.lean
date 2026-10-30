import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStrictHalfSeparatorExcludesCoverPotential
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_three_iff_acyclic_cover_potential_break

Topic: social_choice   Node: e6cb54e2b713

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

The original universal strict Condorcet winning-set bound of three is equivalent to this assertion: for every finite relation with an outside common predecessor for every set of at most three vertices, every positive finite family U of induced acyclic subsets, and every real vertex potential h, some arrow a to b satisfies 2 times the number of members of U containing a plus h(a) strictly less than the size of the family plus h(b). This is an equivalent reformulation and proves neither side.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_dimension_le_three_iff_acyclic_cover_potential_break
    : (∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
        ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S) ↔
      (∀ (m n : ℕ) (R : Fin m → Fin m → Prop)
        (U : Fin n → Finset (Fin m)) (h : Fin m → ℝ), 0 < n →
        (∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) →
        (∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) →
        ∃ a b, R a b ∧
          2 * ((univ.filter fun v => a ∈ U v).card : ℝ) + h a < (n : ℝ) + h b) := by
  classical
  constructor
  · intro hmain m n R U h hn hroot hU
    exact condorcet_strict_half_separator_excludes_cover_potential m n hn R U h hU
      (condorcet_dimension_le_three_iff_acyclic_weight_separation.mp hmain m R hroot)
  · intro hbreak
    apply condorcet_dimension_le_three_iff_acyclic_weight_separation.mpr
    intro m R hroot
    apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
    rintro ⟨n,U,hn,hU,hhalf⟩
    obtain ⟨a,b,hab,hlt⟩ := hbreak m n R U (fun _ => 0) hn hroot hU
    have hle : (n : ℝ) ≤ 2 * ((univ.filter fun v => a ∈ U v).card : ℝ) := by
      exact_mod_cast hhalf a
    simp only [add_zero] at hlt
    exact (not_lt_of_ge hle) hlt
