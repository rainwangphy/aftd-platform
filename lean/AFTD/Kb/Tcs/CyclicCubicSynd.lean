import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicSyndSets

/-!
# cyclic_cubic_synd

Topic: quantum   Node: ad8e26637bdd

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The Nat-level cyclic cubic syndrome is 1 exactly on the members of cyclic_cubic_synd_sets n.
-/

/-- Nat-level cyclic cubic syndrome: T is a cyclic triple. -/
abbrev cyclic_cubic_synd (n : ℕ) (T : Finset ℕ) : Prop := T ∈ cyclic_cubic_synd_sets n
