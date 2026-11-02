import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nExplicitFamily
import AFTD.Kb.Tcs.ThreeTokenK2nLeftCount
import AFTD.Kb.Tcs.ThreeTokenK2nAssembleLayerCover
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# three_token_k2n_assemble_three_layers

Topic: graphs   Node: 858074091911

Provenance: helper lemma. Explicit construction for three_token_k2n_has_dominating_set and OP-666.

If the explicit candidate family has the claimed cardinality and dominates each of the layers with zero, one and two left-part tokens, the required dominating set exists.
-/

theorem three_token_k2n_assemble_three_layers (n : ℕ) (hn : 4 ≤ n)
    (hcard : (three_token_k2n_explicit_family n hn).card ≤ (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2)
    (h0 : ∀ z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3}, three_token_k2n_left_count z = 0 →
      z ∈ three_token_k2n_explicit_family n hn ∨ ∃ w ∈ three_token_k2n_explicit_family n hn,
        (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3).Adj w z)
    (h1 : ∀ z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3}, three_token_k2n_left_count z = 1 →
      z ∈ three_token_k2n_explicit_family n hn ∨ ∃ w ∈ three_token_k2n_explicit_family n hn,
        (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3).Adj w z)
    (h2 : ∀ z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3}, three_token_k2n_left_count z = 2 →
      z ∈ three_token_k2n_explicit_family n hn ∨ ∃ w ∈ three_token_k2n_explicit_family n hn,
        (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3).Adj w z) :
    ∃ S : Finset {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3},
      simple_graph_is_dominating (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3) (S : Set _) ∧
      S.card ≤ (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2 := by
  apply three_token_k2n_assemble_layer_cover n hn hcard
  intro k hk z hz
  interval_cases k
  · exact h0 z hz
  · exact h1 z hz
  · exact h2 z hz
