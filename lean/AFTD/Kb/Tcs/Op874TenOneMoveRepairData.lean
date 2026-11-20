import AFTD.Prelude
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.Bit

/-!
# op874_ten_one_move_repair_data

Topic: graphs   Node: 82482da44766

Provenance: helper lemma. Ten-vertex one-move low-port repair obstruction, experiments 36336 and 36350.

Explicit ten-vertex factor, matching, fixed low ports, allowed one-step changes, and strong-coloring predicate for the repair obstruction.
-/

set_option maxRecDepth 8192
namespace In1098TenRepair
def edges : Finset (Sym2 (Fin 10)) := {s(0,4),s(0,7),s(0,9),s(1,5),s(1,6),s(1,7),s(2,5),s(2,6),s(2,8),s(3,7),s(3,8),s(3,9),s(4,8),s(4,9),s(5,6)}
def next : Fin 10 → Fin 10 := ![7,5,6,8,9,2,1,3,4,0]
def prev : Fin 10 → Fin 10 := ![9,6,5,7,8,1,2,0,3,4]
def mate : Fin 10 → Fin 10 := ![4,7,8,9,0,6,5,1,2,3]
def selected : Fin 10 → Fin 10 := ![4,7,8,9,8,6,1,3,3,4]
def group : Fin 10 → Fin 2 := ![0,1,1,0,0,1,1,0,0,0]
def bit : Fin 10 → Bool := ![true,false,false,false,true,true,true,false,false,false]
def admissible (b : Fin 10 → Bool) (o : Fin 10 → Fin 10) : Prop :=
 (∀ v, b (mate v) = b v) ∧
 (∀ v, o v = mate v ∨ o v = prev v ∨ o v = next v) ∧
 (∀ v, o v = mate v ↔ o (mate v) ≠ v) ∧
 (∀ v, b v = b (next v) → o v = next v ∨ o (next v) = v) ∧
 (∀ v, ¬ (o v = next v ∧ o (next v) = v)) ∧
 (∃ d : Fin 2 → Bool, ∃ ex : Option (Fin 10), ∀ v, o v ≠ mate v →
   ex = some v ∨ (if d (group v) then o v = next v else o v = prev v))
def oneMove (b : Fin 10 → Bool) (o : Fin 10 → Fin 10) : Prop :=
 (b = bit ∧ ∃ v, selected v ≠ mate v ∧
   o v = (if selected v = next v then prev v else next v) ∧ ∀ u, u ≠ v → o u = selected u) ∨
 (b = bit ∧ ∃ v, selected v = mate v ∧ (o v = prev v ∨ o v = next v) ∧ o (mate v) = v ∧
   ∀ u, u ≠ v → u ≠ mate v → o u = selected u) ∨
 (o = selected ∧ ∃ v, b v = !bit v ∧ b (mate v) = !bit (mate v) ∧
   ∀ u, u ≠ v → u ≠ mate v → b u = bit u)
def globallyColorable (b : Fin 10 → Bool) (o : Fin 10 → Fin 10) : Prop :=
 ∃ c h : Fin 10 → Fin 10 → Fin 6,
  (∀ u v, s(u,v) ∈ edges → c u v = c v u ∧
    (if mate u = v then c u v = cycle_matching_low_color (b u) else 2 ≤ (c u v).val)) ∧
  (∀ v x y, s(v,x) ∈ edges → s(v,y) ∈ edges →
    (x ≠ y → c v x ≠ c v y ∧ h v x ≠ h v y) ∧ h v x ≠ c v y) ∧
  (∀ u v x y, s(u,v) ∈ edges → s(u,x) ∈ edges → s(v,y) ∈ edges →
    x ≠ v → y ≠ u → h u x ≠ h v y) ∧
  (∀ v, h v (o v) = cycle_matching_low_color (!b v))
end In1098TenRepair

def op874_ten_one_move_repair_data : Fin 10 → Fin 10 := In1098TenRepair.selected
