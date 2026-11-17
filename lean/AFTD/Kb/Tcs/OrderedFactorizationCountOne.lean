import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedFactorizationCount

/-!
# orderedFactorizationCount_one

Topic: combinatorics   Node: 0f330473a35c

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

H(1) = 1: the empty sequence is the only ordered factorization of 1.
-/

theorem orderedFactorizationCount_one : orderedFactorizationCount 1 = 1 := by
  rw [orderedFactorizationCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨[], by simp⟩, ?_⟩
  rintro ⟨l, hl1, hl2⟩
  ext1
  simp only
  by_contra hne
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha := hl1 a (by simp)
  have : a ∣ 1 := by rw [← hl2]; simp
  have := Nat.le_of_dvd one_pos this
  omega
