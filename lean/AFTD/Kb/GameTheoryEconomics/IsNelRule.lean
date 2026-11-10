import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNelPd

/-!
# is_nel_rule

Topic: fair_division   Node: 8b8c2e152f67

Provenance: formalization of a published result. Source: arXiv:2611.09685, Section 3.1

Given types Agent and Object with decidable equality on Object, an allocation rule f : (Agent → LinearOrder Object) → Agent → Finset Object satisfies is_nel_rule if for every preference profile succ : Agent → LinearOrder Object, the allocation f succ satisfies is_nel_pd with respect to the weak preference relations (fun i => (succ i).le).
-/

/-- An allocation rule satisfies no envy toward larger bundles up to any object (NEL) if at every preference profile its allocation satisfies NEL under pairwise dominance. -/
def is_nel_rule {Agent Object : Type*} [DecidableEq Object]
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop := ∀ succ : Agent → LinearOrder Object, is_nel_pd (fun i => (succ i).le) (f succ)
