import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetUniformOutgoingStationaryCoreObstruction

/-!
# condorcet_minimum_s2_incidence_root_policy_obstruction

Topic: social_choice   Node: 23497ea4257e

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

In the existing eight-vertex globally minimal S3 core, every three-vertex induced S2 core has a unique common root outside it and an acyclic pair of weight three under the incidence recipe with total weight five (one on each core vertex, two on the root). Thus choosing the best minimum-order core and root cannot extend these fixed reciprocal-completion weights to arbitrary directed repairs. This is a recipe obstruction, not a counterexample to the main conjecture.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimum_s2_incidence_root_policy_obstruction
    (D : Finset (Fin 8)) (hD : D.card = 3)
    (hpair : ∀ a ∈ D, ∀ b ∈ D, ∃ c ∈ D,
      condorcet_uniform_outgoing_gap_relation c a ∧
      condorcet_uniform_outgoing_gap_relation c b) :
    ∃ r a : Fin 8, r ∉ D ∧ a ∈ D ∧
      (∀ x, (∀ b ∈ D, condorcet_uniform_outgoing_gap_relation x b) ↔ x = r) ∧
      WellFounded (fun x y : {x : Fin 8 // x ∈ ({r,a} : Finset (Fin 8))} =>
        condorcet_uniform_outgoing_gap_relation x.val y.val) ∧
      (let w : Fin 8 → ℕ := fun x => (if x∈D then 1 else 0) + (if x=r then 2 else 0)
       (∑ x,w x) = 5 ∧ (∑ x∈({r,a} : Finset (Fin 8)),w x) = 3) := by
  have hcert : ∀ D ∈ (univ : Finset (Fin 8)).powerset, D.card = 3 →
      (∀ a∈D,∀ b∈D,∃ c∈D,condorcet_uniform_outgoing_gap_relation c a ∧
        condorcet_uniform_outgoing_gap_relation c b) →
      ∃ r a : Fin 8, r∉D ∧ a∈D ∧
        (∀ x, (∀ b∈D,condorcet_uniform_outgoing_gap_relation x b) ↔ x=r) ∧
        ¬condorcet_uniform_outgoing_gap_relation a r := by decide
  obtain ⟨r,a,hr,ha,hroot,har⟩ := hcert D (mem_powerset.mpr (subset_univ D)) hD hpair
  have hne : r ≠ a := fun h => hr (h ▸ ha)
  have hloop : ∀ x, ¬condorcet_uniform_outgoing_gap_relation x x := by decide
  refine ⟨r,a,hr,ha,hroot,?_,?_⟩
  · refine (measure (fun x : {x : Fin 8 // x∈({r,a} : Finset (Fin 8))} =>
      if x.val=r then 0 else 1)).wf.mono ?_
    intro x y hxy
    have hx := x.property
    have hy := y.property
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact False.elim (hloop r (by simpa only [hx,hy] using hxy))
    · change (if x.val=r then 0 else 1) < (if y.val=r then 0 else 1)
      simp [hx,hy,Ne.symm hne]
    · exact False.elim (har (by simpa only [hx,hy] using hxy))
    · exact False.elim (hloop a (by simpa only [hx,hy] using hxy))
  · dsimp only
    constructor
    · simp [sum_add_distrib,hD]
    · rw [sum_pair hne]
      simp [hr,ha,hne,Ne.symm hne]
