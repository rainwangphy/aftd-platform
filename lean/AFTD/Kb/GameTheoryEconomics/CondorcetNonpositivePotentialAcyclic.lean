import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_nonpositive_potential_acyclic

Topic: social_choice   Node: 74a680fbdca3

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. FourCoverPotential.lean. Structural support constraint on the new equivalent main route. No new election bound or research novelty is claimed.

On a finite directed relation, a vertex set with nonpositive costs is acyclic if a potential drops along arrows by at least the source cost and every zero-cost vertex of the set lies in one induced acyclic set.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_nonpositive_potential_acyclic
    (m : ℕ) (R : Fin m → Fin m → Prop) (A B : Finset (Fin m))
    (c h : Fin m → ℝ)
    (hc : ∀ a ∈ A, c a ≤ 0)
    (hzero : ∀ a ∈ A, c a = 0 → a ∈ B)
    (hlocal : ∀ a b, a ∈ A → b ∈ A → R a b → h b ≤ h a + c a)
    (hB : WellFounded (fun a b : {a : Fin m // a ∈ B} => R a.val b.val)) :
    WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) := by
  classical
  obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
    (fun a b => a ∈ B ∧ R a b)
    (condorcet_acyclic_cover_wellFounded_sources R {a | a ∈ B} hB)
  let L := {x : ℝ // x ∈ Set.range (fun a => -h a)}
  have hwf : WellFounded (fun x y : L => x.val < y.val) :=
    (Set.finite_range (fun a => -h a)).wellFoundedOn
  let q : Fin m → L := fun a => ⟨-h a,⟨a,rfl⟩⟩
  let rank : {a : Fin m // a ∈ A} → L × ℕ := fun a => (q a.val,(σ a.val).val)
  refine ((hwf.prod_lex Nat.lt_wfRel.wf).onFun (f := rank)).mono ?_
  intro a b hab
  have hle := hlocal a b a.property b.property hab
  have hc₀ := hc a a.property
  change Prod.Lex (fun x y : L => x.val < y.val) (fun x y : ℕ => x < y)
    (q a.val,(σ a.val).val) (q b.val,(σ b.val).val)
  by_cases hlt : h b.val < h a.val
  · apply Prod.Lex.left
    change -h a.val < -h b.val
    linarith
  · have heq : h a.val = h b.val := by linarith
    have hca : c a.val = 0 := by linarith
    have hq : q a.val = q b.val := by
      apply Subtype.ext
      change -h a.val = -h b.val
      rw [heq]
    rw [hq]
    apply Prod.Lex.right
    exact hσ a b ⟨hzero a a.property hca,hab⟩
