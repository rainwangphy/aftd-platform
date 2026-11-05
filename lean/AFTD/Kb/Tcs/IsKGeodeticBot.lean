import AFTD.Prelude
import AFTD.Kb.Tcs.IsKGeodetic
import AFTD.Kb.Tcs.IsGeodesic

/-!
# is_k_geodetic_bot

Topic: graphs   Node: 14a934c48cd4

Provenance: helper lemma. arXiv:2611.05762, Definition 1.1

The empty graph on any vertex type V is K-geodetic for every natural number K.
-/

/-- The empty graph is K-geodetic for all K. -/
theorem is_k_geodetic_bot {V : Type*} (K : ℕ) :
    is_k_geodetic (⊥ : SimpleGraph V) K := by
  intro u v huv
  have : IsEmpty {p : (⊥ : SimpleGraph V).Walk u v // is_geodesic p} := ⟨fun ⟨p, _⟩ => by
    cases p with
    | nil => exact huv rfl
    | cons h _ => exact (SimpleGraph.bot_adj _ _).mp h⟩
  simp only [Nat.card_of_isEmpty, Nat.zero_le]
