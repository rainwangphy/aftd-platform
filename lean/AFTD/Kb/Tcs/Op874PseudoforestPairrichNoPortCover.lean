import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges
import AFTD.Kb.Tcs.Op874pfMissing

/-!
# op874_pseudoforest_pairrich_no_port_cover

Topic: graphs   Node: 32c169ae35ea

Provenance: helper lemma. OP-874: four overlapping directed cycles in the pair-rich pseudoforest obstruction.

For the explicit eight-vertex edge and missing-color data, there is no assignment of a distinct port to each missing color at each vertex that covers every edge at which both endpoints miss that color.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private lemma op874pf_cycle_cover {α : Type*} (a b c d p q r s : α)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : p=b ∨ q=a) (hbc : q=c ∨ r=b)
    (hcd : r=d ∨ s=c) (hda : s=a ∨ p=d) :
    (p=b ∧ q=c ∧ r=d ∧ s=a) ∨
      (p=d ∧ q=a ∧ r=b ∧ s=c) := by
  rcases hab with hp | hq
  · have hs : s=a := hda.resolve_right (by simpa only [hp] using hbd)
    have hr : r=d := hcd.resolve_right (by simpa only [hs] using hac)
    have hq : q=c := hbc.resolve_right (by simpa only [hr] using hbd.symm)
    exact Or.inl ⟨hp,hq,hr,hs⟩
  · have hr : r=b := hbc.resolve_left (by simpa only [hq] using hac)
    have hs : s=c := hcd.resolve_left (by simpa only [hr] using hbd)
    have hp : p=d := hda.resolve_left (by simpa only [hs] using hac.symm)
    exact Or.inr ⟨hp,hq,hr,hs⟩

theorem op874_pseudoforest_pairrich_no_port_cover :
    ¬ ∃ p : Fin 8 → Fin 6 → Fin 8,
      (∀ v z w, z ∈ op874pf_missing v → w ∈ op874pf_missing v → z ≠ w → p v z ≠ p v w) ∧
      (∀ u v z, s(u,v) ∈ op874pf_edges → z ∈ op874pf_missing u → z ∈ op874pf_missing v →
        p u z = v ∨ p v z = u) := by
  rintro ⟨p, hinj, hcover⟩
  have h2 := op874pf_cycle_cover (4 : Fin 8) 5 6 7 (p 4 2) (p 5 2) (p 6 2) (p 7 2)
    (by decide) (by decide)
    (hcover 4 5 2 (by decide) (by decide) (by decide))
    (hcover 5 6 2 (by decide) (by decide) (by decide))
    (hcover 6 7 2 (by decide) (by decide) (by decide))
    (hcover 7 4 2 (by decide) (by decide) (by decide))
  have h3 := op874pf_cycle_cover (0 : Fin 8) 3 4 5 (p 0 3) (p 3 3) (p 4 3) (p 5 3)
    (by decide) (by decide)
    (hcover 0 3 3 (by decide) (by decide) (by decide))
    (hcover 3 4 3 (by decide) (by decide) (by decide))
    (hcover 4 5 3 (by decide) (by decide) (by decide))
    (hcover 5 0 3 (by decide) (by decide) (by decide))
  have h4 := op874pf_cycle_cover (0 : Fin 8) 1 2 3 (p 0 4) (p 1 4) (p 2 4) (p 3 4)
    (by decide) (by decide)
    (hcover 0 1 4 (by decide) (by decide) (by decide))
    (hcover 1 2 4 (by decide) (by decide) (by decide))
    (hcover 2 3 4 (by decide) (by decide) (by decide))
    (hcover 3 0 4 (by decide) (by decide) (by decide))
  have h5 := op874pf_cycle_cover (1 : Fin 8) 2 6 7 (p 1 5) (p 2 5) (p 6 5) (p 7 5)
    (by decide) (by decide)
    (hcover 1 2 5 (by decide) (by decide) (by decide))
    (hcover 2 6 5 (by decide) (by decide) (by decide))
    (hcover 6 7 5 (by decide) (by decide) (by decide))
    (hcover 7 1 5 (by decide) (by decide) (by decide))
  have h0 := hinj 0 3 4 (by decide) (by decide) (by decide)
  have h1 := hinj 1 4 5 (by decide) (by decide) (by decide)
  have h2' := hinj 2 4 5 (by decide) (by decide) (by decide)
  have h3' := hinj 3 3 4 (by decide) (by decide) (by decide)
  have h4' := hinj 4 2 3 (by decide) (by decide) (by decide)
  have h5' := hinj 5 2 3 (by decide) (by decide) (by decide)
  have h6' := hinj 6 2 5 (by decide) (by decide) (by decide)
  have h7' := hinj 7 2 5 (by decide) (by decide) (by decide)
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;> simp_all
