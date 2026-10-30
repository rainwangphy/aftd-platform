import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetHeavyPairAcyclicCoverPotentialBreak

/-!
# condorcet_four_acyclic_sets_potential_break

Topic: social_choice   Node: 8b81bc6f8585

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. FourCoverPotential.lean. Structural support constraint on the new equivalent main route. No new election bound or research novelty is claimed.

For every finite S3 relation, every four induced acyclic sets with arbitrary strictly positive real coefficients and every real vertex potential have an arrow violating the weighted half-cover potential inequality. This excludes four positive support sets in this certificate format, without bounding the support needed in the main conjecture.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_four_acyclic_sets_potential_break
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin 4 → Finset (Fin m)) (d : Fin 4 → ℝ) (h : Fin m → ℝ)
    (hd : ∀ v, 0 < d v)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ∃ a b, R a b ∧
      2 * (∑ v, if a ∈ U v then d v else 0) + h a < (∑ v, d v) + h b := by
  classical
  by_cases hpair : d 2+d 3 ≤ d 0+d 1
  · refine condorcet_heavy_pair_acyclic_cover_potential_break m 4 R U d h 0 1 2
      (by decide) (by decide) (by decide) (fun v => (hd v).le) (hd 2) ?_ hroot hU
    simp only [Fin.sum_univ_four]
    linarith
  · refine condorcet_heavy_pair_acyclic_cover_potential_break m 4 R U d h 2 3 0
      (by decide) (by decide) (by decide) (fun v => (hd v).le) (hd 0) ?_ hroot hU
    simp only [Fin.sum_univ_four]
    linarith
