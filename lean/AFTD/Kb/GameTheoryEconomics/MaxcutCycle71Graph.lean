import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field

/-!
# maxcut_cycle71_graph

Topic: equilibria   Node: a2bd0e66ea1c

Provenance: helper lemma. Explicit regular 71-vertex construction for the unweighted minimal-deviation cycle, supported by experiments 12443, 12444, 12450 and 12452.

The explicit 71-vertex finite simple graph with four core blocks of eight and three anchor blocks of thirteen, with edges determined by regular cyclic core relations and the field counts.
-/

def maxcut_cycle71_graph : SimpleGraph (Fin 71) := SimpleGraph.fromRel (fun (u v : Fin 71) =>
  (u.val < 8 ∧ 8 ≤ v.val ∧ v.val < 16 ∧ 2 ≤ (v.val - 8 + 8 - u.val) % 8) ∨
  (u.val < 8 ∧ 16 ≤ v.val ∧ v.val < 24 ∧ (v.val - 16 + 8 - u.val) % 8 < 2) ∨
  (u.val < 8 ∧ 24 ≤ v.val ∧ v.val < 32) ∨
  (8 ≤ u.val ∧ u.val < 16 ∧ 16 ≤ v.val ∧ v.val < 24 ∧
    (v.val - 16 + 8 - (u.val - 8)) % 8 < 4) ∨
  (8 ≤ u.val ∧ u.val < 16 ∧ 24 ≤ v.val ∧ v.val < 32 ∧
    2 ≤ (v.val - 24 + 8 - (u.val - 8)) % 8) ∨
  (u.val < 32 ∧ 32 ≤ v.val ∧ (v.val - 32) % 13 < maxcut_cycle71_field u.val ((v.val - 32) / 13)))
