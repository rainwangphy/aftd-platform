import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nExplicitFamily
import AFTD.Kb.Tcs.ThreeTokenK2nLeftCount
import AFTD.Kb.Tcs.ThreeTokenK2nLeftCountLeTwo
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# three_token_k2n_assemble_layer_cover

Topic: graphs   Node: 44c7ba9db039

Provenance: helper lemma. Explicit construction for three_token_k2n_has_dominating_set and OP-666.

If the explicit candidate family has the claimed cardinality and dominates every configuration in each of the three possible left-token layers, it is a dominating set of the claimed size.
-/

theorem three_token_k2n_assemble_layer_cover (n : ℕ) (hn : 4 ≤ n)
    (hcard : (three_token_k2n_explicit_family n hn).card ≤ (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2)
    (hlayer : ∀ k ≤ 2, ∀ z : {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3},
      three_token_k2n_left_count z = k →
      z ∈ three_token_k2n_explicit_family n hn ∨ ∃ w ∈ three_token_k2n_explicit_family n hn,
        (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3).Adj w z) :
    ∃ S : Finset {s : Finset (Fin 2 ⊕ Fin n) // s.card = 3},
      simple_graph_is_dominating (token_graph (completeBipartiteGraph (Fin 2) (Fin n)) 3) (S : Set _) ∧
      S.card ≤ (n / 2).choose 2 + (n - n / 2).choose 2 + n - 2 := by
  refine ⟨three_token_k2n_explicit_family n hn, ?_, hcard⟩
  intro z
  exact hlayer (three_token_k2n_left_count z) (three_token_k2n_left_count_le_two z) z rfl
