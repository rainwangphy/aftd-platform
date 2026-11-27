import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BadPortsUnselectedMatchingCrosses

/-!
# op874_bad_port_palette_gives_graph_bipartition

Topic: graphs   Node: f4cad192dc46

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

A graph covered by three neighbor maps is two-colorable if the original and selected maps cross the Boolean partition and the involutive unselected map satisfies the displayed all-bad palette and interface hypotheses.
-/

theorem op874_bad_port_palette_gives_graph_bipartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (flag : V → Bool) (mate selected other : V → V)
    (t s x y : V → Fin 6)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (hselected : ∀ v, flag (selected v) = !flag v)
    (hother : ∀ v, other (other v) = v)
    (htsame : ∀ v, t (other v) = t v)
    (hlocal : ∀ v, flag v = false →
      2 ≤ (t v).val ∧ (t v).val ≤ 3 ∧ 4 ≤ (s v).val ∧ 4 ≤ (x v).val ∧
      2 ≤ (y v).val ∧ s v ≠ x v ∧ y v ≠ s v ∧ y v ≠ x v ∧ y v ≠ t v)
    (hcross : ∀ v, flag v = false → flag (other v) = false → y v ≠ y (other v))
    (hcover : ∀ u v, G.Adj u v → v = mate u ∨ v = selected u ∨ v = other u) :
    ∃ f : V → Bool, ∀ u v, G.Adj u v → f u ≠ f v := by
  have hthird := op874_bad_ports_unselected_matching_crosses flag mate other t s x y
    hmate hflip hother htsame hlocal hcross
  refine ⟨flag, ?_⟩
  intro u v huv
  rcases hcover u v huv with h | h | h
  · rw [h, hflip]
    cases flag u <;> decide
  · rw [h, hselected]
    cases flag u <;> decide
  · rw [h, hthird]
    cases flag u <;> decide
