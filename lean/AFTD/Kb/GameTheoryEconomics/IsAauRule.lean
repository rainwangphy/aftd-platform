import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_aau_rule

Topic: fair_division   Node: 7b48c1703d2e

Provenance: formalization of a published result. Source: scout/2611-09685-who-picks-first-compensatory-fairness-when-equal-division-i.md:280

An allocation rule satisfies alternating advantage under unanimity (AAU) if at every unanimous preference profile, for any two agents i and j receiving bundles of equal size and every step t, whichever agent has the more preferred object at step t has the less preferred object at step t + 1.
-/

/-- An allocation rule satisfies AAU if at every unanimous profile, between agents of equal bundle size, advantage strictly alternates from step to step. -/
def is_aau_rule {Agent Object : Type*}
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop := ∀ (u_order : LinearOrder Object) (i j : Agent),
  ∀ (hcard : (f (fun _ => u_order) i).card = (f (fun _ => u_order) j).card),
    let _ := u_order
    let li := (f (fun _ => u_order) i).sort (· ≥ ·)
    let lj := (f (fun _ => u_order) j).sort (· ≥ ·)
    ∀ (t : ℕ) (ht : t + 1 < (f (fun _ => u_order) i).card),
      li.get ⟨t, by rw [Finset.length_sort]; omega⟩ > lj.get ⟨t, by rw [Finset.length_sort]; omega⟩ →
      lj.get ⟨t + 1, by rw [Finset.length_sort]; omega⟩ > li.get ⟨t + 1, by rw [Finset.length_sort]; omega⟩
