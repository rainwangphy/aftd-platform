import AFTD.Prelude
import AFTD.Kb.Tcs.IsKTight
import AFTD.Kb.Tcs.GStableKneser

/-!
# not_is_k_tight_empty

Topic: graphs   Node: 8312cf8e6b0b

Provenance: helper lemma. arXiv:2610.17884 Sec. 1 -- The chromatic number of G-stable Kneser graphs

The empty graph on 0 vertices is not k-tight for any k ≥ 2.
-/

/-- The empty graph on 0 vertices is not k-tight for any k ≥ 2. -/
lemma not_is_k_tight_empty (k : ℕ) (hk : 2 ≤ k) :
    ¬ is_k_tight (⊥ : SimpleGraph Empty) k := by
  unfold is_k_tight
  haveI : IsEmpty { s : Finset Empty // (⊥ : SimpleGraph Empty).IsNIndepSet k s } := by
    constructor
    rintro ⟨s, hs⟩
    have hcard : s.card = k := hs.card_eq
    have hz : s.card = 0 := by
      rw [Finset.card_eq_zero]
      ext x
      exact x.elim
    omega
  rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
  have hrhs : Fintype.card Empty - 2 * k + 2 = 2 := by
    have h0 : Fintype.card Empty = 0 := by simp
    omega
  rw [hrhs]
  simp
