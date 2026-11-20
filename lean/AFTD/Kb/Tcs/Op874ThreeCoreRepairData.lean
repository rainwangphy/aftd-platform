import AFTD.Prelude
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.Bit

/-!
# op874_three_core_repair_data

Topic: graphs   Node: a4486f68cd69

Provenance: helper lemma. Three independent uniform-port local obstructions joined along matching edges, experiments 36363 and 36366.

Explicit 30-vertex factor, matching, fixed low ports, allowed one-step changes, and strong-coloring predicate for the three-core repair obstruction.
-/

set_option maxRecDepth 8192
namespace In1098ThreeCore
def edges : Finset (Sym2 (Fin 30)) := {s(0,6),s(0,8),s(0,13),s(1,5),s(1,8),s(1,9),s(2,4),s(2,5),s(2,7),s(3,4),s(3,5),s(3,10),s(4,7),s(6,7),s(6,9),s(8,9),s(10,16),s(10,18),s(11,18),s(11,19),s(11,25),s(12,14),s(12,15),s(12,17),s(13,14),s(13,15),s(14,17),s(15,21),s(16,17),s(16,19),s(18,19),s(20,23),s(20,26),s(20,28),s(21,28),s(21,29),s(22,24),s(22,25),s(22,27),s(23,24),s(23,25),s(24,27),s(26,27),s(26,29),s(28,29)}
def next : Fin 30 → Fin 30 := ![6,8,5,4,7,3,9,2,0,1,16,18,15,14,17,13,19,12,10,11,26,28,25,24,27,23,29,22,20,21]
def prev : Fin 30 → Fin 30 := ![8,9,7,5,3,2,0,4,1,6,18,19,17,15,13,12,10,14,11,16,28,29,27,25,23,22,20,24,21,26]
def mate : Fin 30 → Fin 30 := ![13,5,4,10,2,1,7,6,9,8,3,25,14,0,12,21,17,16,19,18,23,15,24,20,22,11,27,26,29,28]
def selected : Fin 30 → Fin 30 := ![6,8,5,10,2,1,9,6,0,8,16,18,15,0,12,21,19,16,10,18,26,28,25,20,22,11,29,26,20,28]
def group : Fin 30 → Fin 6 := ![0,0,1,1,1,1,0,1,0,0,2,2,3,3,3,3,2,3,2,2,4,4,5,5,5,5,4,5,4,4]
def bit : Fin 30 → Bool := ![true,false,false,true,false,false,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,false,false,true,false,false,true,true,true,true]
def admissible (b : Fin 30 → Bool) (o : Fin 30 → Fin 30) : Prop :=
 (∀ v, b (mate v) = b v) ∧
 (∀ v, o v = mate v ∨ o v = prev v ∨ o v = next v) ∧
 (∀ v, o v = mate v ↔ o (mate v) ≠ v) ∧
 (∀ v, b v = b (next v) → o v = next v ∨ o (next v) = v) ∧
 (∀ v, ¬ (o v = next v ∧ o (next v) = v)) ∧
 (∃ d : Fin 6 → Bool, ∃ ex : Option (Fin 30), ∀ v, o v ≠ mate v →
   ex = some v ∨ (if d (group v) then o v = next v else o v = prev v))
def oneMove (b : Fin 30 → Bool) (o : Fin 30 → Fin 30) : Prop :=
 (b = bit ∧ ∃ v, selected v ≠ mate v ∧
   o v = (if selected v = next v then prev v else next v) ∧ ∀ u, u ≠ v → o u = selected u) ∨
 (b = bit ∧ ∃ v, selected v = mate v ∧ (o v = prev v ∨ o v = next v) ∧ o (mate v) = v ∧
   ∀ u, u ≠ v → u ≠ mate v → o u = selected u) ∨
 (o = selected ∧ ∃ v, b v = !bit v ∧ b (mate v) = !bit (mate v) ∧
   ∀ u, u ≠ v → u ≠ mate v → b u = bit u)
def globallyColorable (b : Fin 30 → Bool) (o : Fin 30 → Fin 30) : Prop :=
 ∃ c h : Fin 30 → Fin 30 → Fin 6,
  (∀ u v, s(u,v) ∈ edges → c u v = c v u ∧
    (if mate u = v then c u v = cycle_matching_low_color (b u) else 2 ≤ (c u v).val)) ∧
  (∀ v x y, s(v,x) ∈ edges → s(v,y) ∈ edges →
    (x ≠ y → c v x ≠ c v y ∧ h v x ≠ h v y) ∧ h v x ≠ c v y) ∧
  (∀ u v x y, s(u,v) ∈ edges → s(u,x) ∈ edges → s(v,y) ∈ edges →
    x ≠ v → y ≠ u → h u x ≠ h v y) ∧
  (∀ v, h v (o v) = cycle_matching_low_color (!b v))
end In1098ThreeCore

def op874_three_core_repair_data : Fin 30 → Fin 30 := In1098ThreeCore.selected
