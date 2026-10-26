import AFTD.Prelude
import AFTD.Kb.Tcs.IsPkFree

/-!
# is_pk_free_of_card_lt

Topic: graphs   Node: 6363c7cc0c6f

Provenance: helper lemma. step towards p7_claw_free_dominating_pair_of_no_hole

Any simple graph on fewer than k vertices is P_k-free, as an induced embedding requires an injection from Fin k into V.
-/

/-- A graph on fewer than k vertices cannot contain an induced P_k. -/
theorem is_pk_free_of_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h : Fintype.card V < k) : IsPkFree G k := by
  intro hc
  rcases hc with ⟨f⟩
  have h1 := Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at h1
  omega
