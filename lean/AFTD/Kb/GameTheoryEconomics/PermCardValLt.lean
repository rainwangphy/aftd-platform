import AFTD.Prelude

/-!
# perm_card_val_lt

Topic: matching_markets   Node: f4ccdf59c7b8

For a permutation s of {0, ..., n-1} and c in {0, ..., n-1}, exactly c elements x have s(x) < c.
-/

theorem perm_card_val_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n) :
    (Finset.univ.filter fun x : Fin n => (σ x : ℕ) < c).card = c := by
  have h1 : (Finset.univ.filter fun x : Fin n => (σ x : ℕ) < c) =
      (Finset.Iio c).map σ.symm.toEmbedding := by
    ext x
    simp [Finset.mem_map_equiv]
  rw [h1, Finset.card_map, Fin.card_Iio]
