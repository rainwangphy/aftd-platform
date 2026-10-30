import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFiniteStrictSeparatorIntegerWeights
import AFTD.Kb.GameTheoryEconomics.CondorcetIntegerAcyclicSeparatorNeighborMass
import AFTD.Kb.GameTheoryEconomics.CondorcetIntegerCirculationOfNeighborMass

/-!
# condorcet_strict_half_separator_iff_integer_circulation

Topic: social_choice   Node: 60af2c6d5ea3

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

For every finite directed relation, existence of nonnegative real weights putting every induced acyclic subset strictly below half their total is equivalent to existence of nonnegative integer edge multiplicities, zero off the relation and balanced at every vertex, whose outgoing vertex marginals put every induced acyclic subset strictly below half their total. This is a strict-half equivalence, not equality of unrestricted and circulation optima at arbitrary thresholds; it does not construct a separator on S3 relations.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_strict_half_separator_iff_integer_circulation
    (m : ℕ) (R : Fin m → Fin m → Prop) :
    (∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a) ↔
    (∃ f : Fin m → Fin m → ℕ,
      (∀ a b, ¬ R a b → f a b = 0) ∧
      (∀ a, ∑ b, f a b = ∑ b, f b a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, ∑ b, f a b) < ∑ a, ∑ b, f a b) := by
  classical
  constructor
  · rintro ⟨w,hw,hsep⟩
    obtain ⟨d,hd⟩ := condorcet_finite_strict_separator_integer_weights m
      (fun A => WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val))
      w hw hsep
    obtain ⟨v,hv,hHall⟩ := condorcet_integer_acyclic_separator_neighbor_mass m R d hd
    obtain ⟨f,hf,hrow,hcol⟩ := condorcet_integer_circulation_of_neighbor_mass m R v hHall
    refine ⟨f,hf,?_,?_⟩
    · intro a
      rw [hrow,hcol]
    · intro A hA
      simpa only [hrow] using hv A hA
  · rintro ⟨f,_,_,hf⟩
    refine ⟨fun a => ((∑ b, f a b : ℕ) : ℝ),fun a => Nat.cast_nonneg _,?_⟩
    intro A hA
    dsimp only
    exact_mod_cast hf A hA
