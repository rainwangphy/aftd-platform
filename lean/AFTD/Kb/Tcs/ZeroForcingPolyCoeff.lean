import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_poly_coeff

Topic: graphs   Node: eec979854ba1

Provenance: helper lemma. step towards gt_zero_forcing_poly_not_unimodal

The coefficient of x^k in the zero forcing polynomial of G is the number of k-element vertex subsets that are zero forcing sets.
-/

theorem zero_forcing_poly_coeff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    (zero_forcing_poly G).coeff k =
      {S : Finset V | is_zero_forcing_set G (S : Set V) ∧ S.card = k}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have hfilter : ({S : Finset V | is_zero_forcing_set G (S : Set V) ∧ S.card = k} : Set (Finset V)).toFinset =
      Finset.univ.filter (fun S : Finset V => is_zero_forcing_set G (S : Set V) ∧ S.card = k) := by
    ext S
    simp
  rw [hfilter, Finset.card_filter]
  unfold zero_forcing_poly
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hz : is_zero_forcing_set G (S : Set V)
  · by_cases hk : S.card = k
    · simp [hz, hk, Polynomial.coeff_X_pow]
    · simp [hz, hk, Polynomial.coeff_X_pow, Ne.symm hk]
  · simp [hz]
