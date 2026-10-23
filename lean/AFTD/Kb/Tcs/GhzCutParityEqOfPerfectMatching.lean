import AFTD.Prelude
import AFTD.Kb.Tcs.GhzEvenCardOfPerfectMatching
import AFTD.Kb.Tcs.GhzIsPerfectMatching

/-!
# ghz_cut_parity_eq_of_perfect_matching

Topic: quantum   Node: 0e15d5031d14

Provenance: helper lemma. arXiv:2610.22190 Section 4

For any finite type V with decidable equality and any simple graph G on V with a perfect matching M (ghz_is_perfect_matching G M), the cardinality of any subset S : Finset V and the cardinality of its complement Sᶜ have the same parity modulo 2.
-/

/-- In a finite graph with a perfect matching, both sides of any vertex cut have the same parity. -/
lemma ghz_cut_parity_eq_of_perfect_matching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : ghz_is_perfect_matching G M)
    (S : Finset V) :
    S.card % 2 = (Sᶜ : Finset V).card % 2 := by
  have h := ghz_even_card_of_perfect_matching G M hM
  rw [Nat.even_iff] at h
  have hsum : S.card + (Sᶜ : Finset V).card = Fintype.card V := Finset.card_add_card_compl S
  omega
