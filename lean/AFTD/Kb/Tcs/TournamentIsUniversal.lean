import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_is_universal

Topic: graphs   Node: 4b930e49895a

Provenance: formalization of a published result. Source: arXiv:2610.06891 Section 1

A directed graph T on vertex type V is k-universal if for every tournament H on Fin k, there exists an embedding f : Fin k ↪ V such that for all vertices u, v of H, T has an arc from f u to f v if and only if H has an arc from u to v.
-/

/-- A digraph T is k-universal if every tournament on Fin k embeds into T. -/
def tournament_is_universal (k : ℕ) {V : Type*} (T : Digraph V) : Prop := ∀ (H : Digraph (Fin k)), digraph_is_tournament H →
    ∃ f : Fin k ↪ V, ∀ u v, T.Adj (f u) (f v) ↔ H.Adj u v
