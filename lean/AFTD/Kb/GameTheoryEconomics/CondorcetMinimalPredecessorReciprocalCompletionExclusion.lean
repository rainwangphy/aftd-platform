import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorCoalitionCompletionExclusion

/-!
# condorcet_minimal_predecessor_reciprocal_completion_exclusion

Topic: social_choice   Node: 7838413ace0d

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

Let a globally minimal finite S_k core, k positive, map by a relation-preserving function into another finite relation. If every undominated (k+1)-set of the core has a common reciprocal neighbor in the larger relation, the larger relation admits no positive finite acyclic half-cover. Injectivity of the map is not required.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimal_predecessor_reciprocal_completion_exclusion
    (m q n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (R : Fin m → Fin m → Prop) (H : Fin q → Fin q → Prop) (f : Fin m → Fin q)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (hmap : ∀ a b, R a b → H (f a) (f b))
    (hrepair : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) →
      ∃ x : Fin q, ∀ a ∈ T, H x (f a) ∧ H (f a) x)
    (U : Fin n → Finset (Fin q))
    (hU : ∀ v, WellFounded (fun a b : {a : Fin q // a ∈ U v} => H a.val b.val))
    (hhalf : ∀ a, n ≤ 2*(univ.filter fun v => a∈U v).card) : False := by
  classical
  let V : Fin n → Finset (Fin m) := fun v => univ.filter fun a => f a ∈ U v
  apply condorcet_minimal_predecessor_coalition_completion_exclusion m n k hn hk R
    hroot hminimal V
  · intro v
    let g : {a : Fin m // a∈V v} → {a : Fin q // a∈U v} :=
      fun a => ⟨f a.val,(mem_filter.mp a.property).2⟩
    exact (InvImage.wf g (hU v)).mono (fun a b hab => hmap a b hab)
  · intro a
    simpa [V] using hhalf (f a)
  · intro T hT hbad
    obtain ⟨x,hx⟩ := hrepair T hT hbad
    refine ⟨univ.filter (fun v => x ∈ U v),hhalf x,?_⟩
    intro v hv a ha hmem
    have hxU := (mem_filter.mp hv).2
    have haU := (mem_filter.mp hmem).2
    exact (hU v).asymmetric (a := ⟨x,hxU⟩) (b := ⟨f a,haU⟩) (hx a ha).1 (hx a ha).2
