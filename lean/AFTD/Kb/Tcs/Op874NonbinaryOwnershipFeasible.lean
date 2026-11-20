import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NonbinaryEdges
import AFTD.Kb.Tcs.Op874NonbinaryMatching
import AFTD.Kb.Tcs.Op874NonbinaryBit
import AFTD.Kb.Tcs.Op874NonbinaryMatchingFirst
import AFTD.Kb.Tcs.Op874NonbinaryMatchingSecond

/-!
# op874_nonbinary_ownership_feasible

Topic: graphs   Node: a1fb0ae9c3ee

Provenance: helper lemma. Finite global ownership nonbinary obstruction in the OP-874 campaign.

A strong two-versus-four local-state coloring on the fixed graph with exactly the prescribed first-endpoint matching ownership.
-/

def op874_nonbinary_ownership_feasible (own : Fin 8 → Bool) : Prop := ∃ c h : Fin 16 → Fin 16 → Fin 6,
    (∀ u v, s(u,v) ∈ op874_nonbinary_edges →
      c u v = c v u ∧
      (if s(u,v) ∈ op874_nonbinary_matching then
        c u v = (if op874_nonbinary_bit u then 1 else 0)
       else 2 ≤ (c u v).val)) ∧
    (∀ v x y, s(v,x) ∈ op874_nonbinary_edges → s(v,y) ∈ op874_nonbinary_edges →
      (x ≠ y → c v x ≠ c v y ∧ h v x ≠ h v y) ∧ h v x ≠ c v y) ∧
    (∀ u v x y, s(u,v) ∈ op874_nonbinary_edges → s(u,x) ∈ op874_nonbinary_edges →
      s(v,y) ∈ op874_nonbinary_edges → x ≠ v → y ≠ u → h u x ≠ h v y) ∧
    (∀ i, let u := op874_nonbinary_matching_first i
      let v := op874_nonbinary_matching_second i
      (h u v = (if op874_nonbinary_bit u then 0 else 1) ↔ own i = true) ∧
      (h v u = (if op874_nonbinary_bit v then 0 else 1) ↔ own i = false))
