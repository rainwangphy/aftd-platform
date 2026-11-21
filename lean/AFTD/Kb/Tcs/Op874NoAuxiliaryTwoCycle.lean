import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NoEvenAuxiliaryCycle

/-!
# op874_no_auxiliary_two_cycle

Topic: graphs   Node: 062fb954f430

Provenance: helper lemma. The no-even-cycle lemma excludes directed two-cycles.

In a strongly connected no-even auxiliary graph, two distinct vertices cannot be joined by arcs in both directions.
-/

theorem op874_no_auxiliary_two_cycle {X : Type*} [Fintype X] [DecidableEq X]
    (p q : Equiv.Perm X)
    (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v)
    (hno : ∀ b : X → Bool, ∃ x, b x = b (p x) ∧ b x = b (q x))
    (r x : X) (hne : r ≠ x) (hrx : p r = x ∨ q r = x) (hxr : p x = r ∨ q x = r) : False := by
  apply op874_no_even_auxiliary_cycle p q hstrong hno 2 (by decide) (![r,x] : Fin 2 → X)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simp_all
