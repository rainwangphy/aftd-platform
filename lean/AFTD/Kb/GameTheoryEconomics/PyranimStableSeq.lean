import AFTD.Prelude

/-!
# pyranim_stable_seq

Topic: combinatorial_games   Node: 7e07dc971a70

Provenance: helper lemma. step towards pyranim_card_stable_positions

For a set X of chips, pyranim_stable_seq n X is the column-minimum sequence l i = (i+1) + 1 - (number of a in {1,...,i+1} with (a, i+1) in X), i.e. the least a with (a, i+1) in X when the column is nonempty and i+2 when it is empty.
-/

/-- The column-minimum sequence of a position: l i = (i+2) - (number of chips in column i+1). -/
noncomputable def pyranim_stable_seq (n : ℕ) (X : Finset (ℕ × ℕ)) : Fin n → Fin (n + 2) := fun i => ⟨(i : ℕ) + 2 - ((Finset.Icc 1 ((i : ℕ) + 1)).filter (fun a => (a, (i : ℕ) + 1) ∈ X)).card, by
    have h : ((Finset.Icc 1 ((i : ℕ) + 1)).filter (fun a => (a, (i : ℕ) + 1) ∈ X)).card ≤ (i : ℕ) + 1 := by
      have h2 := Finset.card_filter_le (s := Finset.Icc 1 ((i : ℕ) + 1))
        (fun a => (a, (i : ℕ) + 1) ∈ X)
      rw [Nat.card_Icc] at h2
      omega
    omega⟩
