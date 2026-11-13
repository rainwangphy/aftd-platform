import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_complements_three_extendible

Topic: graphs   Node: bcce9bbcde4f

Provenance: helper lemma. A natural strengthening of the exchange condition considered for OP-1399.

The complements of zero forcing sets form a three-extendible independence system.
-/

def zero_forcing_complements_three_extendible {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop := ∀ A B : Finset V, A ⊆ B → is_zero_forcing_set G ((Finset.univ \ A : Finset V) : Set V) → is_zero_forcing_set G ((Finset.univ \ B : Finset V) : Set V) → ∀ x : V, x ∉ B → is_zero_forcing_set G ((Finset.univ \ insert x A : Finset V) : Set V) → ∃ R : Finset V, R ⊆ B \ A ∧ R.card ≤ 3 ∧ is_zero_forcing_set G ((Finset.univ \ insert x (B \ R) : Finset V) : Set V)
