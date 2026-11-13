import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_complements_two_extendible

Topic: graphs   Node: 52c875b8aa49

Provenance: helper lemma. A test of the two-matroid-intersection route to tree_zero_forcing_poly_unimodal; see experiments 24677 and 24688.

Complements of zero forcing sets have the two-extendibility property: whenever A is contained in B, x is outside B, and A, B and A union {x} are complements of zero forcing sets, some R contained in B minus A has at most two elements and (B minus R) union {x} is also a complement of a zero forcing set.
-/

def zero_forcing_complements_two_extendible {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop := ∀ A B : Finset V, A ⊆ B → is_zero_forcing_set G ((Finset.univ \ A : Finset V) : Set V) → is_zero_forcing_set G ((Finset.univ \ B : Finset V) : Set V) → ∀ x : V, x ∉ B → is_zero_forcing_set G ((Finset.univ \ insert x A : Finset V) : Set V) → ∃ R : Finset V, R ⊆ B \ A ∧ R.card ≤ 2 ∧ is_zero_forcing_set G ((Finset.univ \ insert x (B \ R) : Finset V) : Set V)
