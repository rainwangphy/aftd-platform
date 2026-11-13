import AFTD.Prelude

/-!
# is_braid_solution

Topic: combinatorics   Node: c8a69b9a5078

Provenance: formalization of a published result. Source: scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:135

A map R : X × X → X × X on a type X is a solution of the braid equation if (R × id) ∘ (id × R) ∘ (R × id) = (id × R) ∘ (R × id) ∘ (id × R) on X × X × X.
-/

/-- Predicate stating that a map R : X × X → X × X satisfies the braid relation on X³. -/
def is_braid_solution {X : Type*} (R : X × X → X × X) : Prop :=
  let R12 : X × X × X → X × X × X := fun (x, y, z) => ((R (x, y)).1, (R (x, y)).2, z)
  let R23 : X × X × X → X × X × X := fun (x, y, z) => (x, (R (y, z)).1, (R (y, z)).2)
  R12 ∘ R23 ∘ R12 = R23 ∘ R12 ∘ R23
