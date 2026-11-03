import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExistsStrictlyOrderedIntervals
import AFTD.Kb.GameTheoryEconomics.LexStreamOrderEmbeddingOfIntervals
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# countable_lex_stream_order_embedding_exists

Topic: social_choice   Node: 09fc5d7a9416

Provenance: helper lemma. step towards swf_anonymous_stationary_monotone_upper_lower_dominance_exists

Every lexicographic stream space over a countable linearly ordered alphabet admits an order embedding into the real line.
-/

/-- Every lexicographic stream space over a countable linearly ordered alphabet admits an order embedding into the real line (Dubey et al. 2026, Lemma 1). -/
theorem countable_lex_stream_order_embedding_exists
    (A : Type) [LinearOrder A] [Countable A] :
    ∃ Φ : Lex (ℕ → A) → ℝ, ∀ u v : Lex (ℕ → A), u ≤ v ↔ Φ u ≤ Φ v := by
  obtain ⟨l, r, ⟨h1, h2⟩⟩ := exists_strictly_ordered_intervals (A := A)
  exact lex_stream_order_embedding_of_intervals l r (fun a => (h1 a).1) (fun a => (h1 a).2.1)
    (fun a => (h1 a).2.2) h2
