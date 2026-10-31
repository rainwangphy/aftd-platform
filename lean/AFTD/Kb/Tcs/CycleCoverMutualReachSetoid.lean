import AFTD.Prelude

/-!
# cycle_cover_mutual_reach_setoid

Topic: graphs   Node: ee20db2a709a

Provenance: helper lemma. step towards cycle_cover_diameter_of_strongly_connected_components

The setoid of mutual reachability along a relation R: x ~ y iff x reaches y and y reaches x by an R-path. Its quotient is the set of strongly connected components; it does not require R to be reflexive.
-/

/-- Setoid of mutual reachability along R; its quotient is the set of strongly connected components. -/
def cycle_cover_mutual_reach_setoid {V : Type} (R : V → V → Prop) : Setoid V where
  r x y := Relation.ReflTransGen R x y ∧ Relation.ReflTransGen R y x
  iseqv := ⟨fun _ => ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩⟩
