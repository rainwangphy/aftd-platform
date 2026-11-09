import AFTD.Prelude

/-!
# is_neutral_rule

Topic: fair_division   Node: a17f0ccf1623

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 2.3

Given types Agent and Object with decidable equality on Object, a rule f : (Agent -> LinearOrder Object) -> Agent -> Finset Object satisfies is_neutral_rule if for every profile succ : Agent -> LinearOrder Object, every permutation σ : Equiv.Perm Object, and every agent i : Agent, the finite bundle f (fun j => @Equiv.linearOrder Object Object σ.symm (succ j) _) i equals the image under σ of the finite bundle f succ i, namely (f succ i).map σ.toEmbedding.
-/

/-- A rule is neutral if permuting objects permutes the assigned bundles accordingly. -/
def is_neutral_rule {Agent Object : Type*} [DecidableEq Object]
    (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop :=
  ∀ (succ : Agent → LinearOrder Object) (σ : Equiv.Perm Object) (i : Agent),
    f (fun j => @Equiv.linearOrder Object Object σ.symm (succ j) _) i =
      (f succ i).map σ.toEmbedding
