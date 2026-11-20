import AFTD.Prelude
import AFTD.Kb.Tcs.CycleMatchingLowColor

/-!
# op874_low_ports_globally_colorable

Topic: graphs   Node: 54ee946df9b9

Provenance: helper lemma. Matching-palette and fixed low-port model, experiments 36363–36374.

A strong two-versus-four local-state coloring on a finite edge set with fixed matching bits and selected low ports.
-/

def op874_low_ports_globally_colorable {n : ℕ} (E : Finset (Sym2 (Fin n))) (mate : Equiv.Perm (Fin n)) (b : Fin n → Bool) (o : Fin n → Fin n) : Prop := ∃ c h : Fin n → Fin n → Fin 6,
  (∀ u v, s(u,v) ∈ E → c u v = c v u ∧
    (if mate u = v then c u v = cycle_matching_low_color (b u) else 2 ≤ (c u v).val)) ∧
  (∀ v x y, s(v,x) ∈ E → s(v,y) ∈ E →
    (x ≠ y → c v x ≠ c v y ∧ h v x ≠ h v y) ∧ h v x ≠ c v y) ∧
  (∀ u v x y, s(u,v) ∈ E → s(u,x) ∈ E → s(v,y) ∈ E → x ≠ v → y ≠ u → h u x ≠ h v y) ∧
  (∀ v, h v (o v) = cycle_matching_low_color (!b v))
