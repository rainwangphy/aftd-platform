import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_acyclic_cover_uniformize

Topic: social_choice   Node: 955686f27778

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

An acyclic family covering every vertex at least q times can be trimmed, independently at each vertex, to an acyclic subfamily with exactly q memberships per vertex. The relation is unchanged.
-/

open Finset
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000

theorem condorcet_acyclic_cover_uniformize
    (m n q : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hcover : ∀ a, q ≤ (univ.filter fun v => a ∈ U v).card) :
    ∃ V : Fin n → Finset (Fin m),
      (∀ v, V v ⊆ U v) ∧
      (∀ v, WellFounded (fun a b : {a : Fin m // a ∈ V v} => R a.val b.val)) ∧
      (∀ a, (univ.filter fun v => a ∈ V v).card = q) := by
  classical
  have hex : ∀ a : Fin m, ∃ S : Finset (Fin n),
      S ⊆ univ.filter (fun v => a ∈ U v) ∧ S.card = q := by
    intro a
    exact exists_subset_card_eq (hcover a)
  choose S hsub hcard using hex
  let V : Fin n → Finset (Fin m) := fun v => univ.filter fun a => v ∈ S a
  have hVU : ∀ v, V v ⊆ U v := by
    intro v a ha
    exact (mem_filter.mp (hsub a (mem_filter.mp ha).2)).2
  refine ⟨V,hVU,?_,?_⟩
  · intro v
    exact InvImage.wf (fun a : {a : Fin m // a ∈ V v} =>
      (⟨a.val,hVU v a.property⟩ : {a : Fin m // a ∈ U v})) (hU v)
  · intro a
    have heq : univ.filter (fun v => a ∈ V v) = S a := by
      ext v
      simp [V]
    rw [heq,hcard]
