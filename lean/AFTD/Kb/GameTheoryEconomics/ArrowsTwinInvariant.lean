import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_twin_invariant

Topic: combinatorial_games   Node: cafd24bc8168

Provenance: helper lemma. step towards arrows_twin_branch_reduction

The pairing invariant of the second player on the disjoint sum of T and T' in the twin-branch configuration: the marked edges of the two twin branches B₁ and B₂ are matched by an orientation-reversing correspondence along φ, the shared part H of the two boards carries identical marks, and the new pendant edge of T' is unmarked.
-/

/-- The invariant maintained by the second player's pairing strategy on the sum of T with its twin-branch reduction. -/
def arrows_twin_invariant {V : Type*} (T : SimpleGraph V) (c : V) (B₁ B₂ : Set V)
    (φ : T.induce (B₁ ∪ {c}) ≃g T.induce (B₂ ∪ {c}))
    (p : ArrowsPos V) (q : ArrowsPos (Option ↥((B₁ ∪ B₂)ᶜ : Set V))) : Prop := (∀ u v : ↥(B₁ ∪ {c}), p.1 (u : V) (v : V) =
      p.1 ((φ v : ↥(B₂ ∪ {c})) : V) ((φ u : ↥(B₂ ∪ {c})) : V)) ∧
  (∀ u v : ↥((B₁ ∪ B₂)ᶜ : Set V), p.1 (u : V) (v : V) = q.1 (some u) (some v)) ∧
  (∀ u : ↥((B₁ ∪ B₂)ᶜ : Set V), q.1 none (some u) = false ∧ q.1 (some u) none = false)
