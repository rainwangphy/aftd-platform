import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureWinnerProb
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureWinnerLoserProb
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner
import AFTD.Kb.GameTheoryEconomics.CondorcetLoser
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.ImpartialCultureProb

/-!
# condorcet_three_winner_prob_eq_both_prob

Topic: social_choice   Node: 5161bf656d50

Provenance: helper lemma. Guilbaud 1952

For any odd number of voters k, the probability under impartial culture that a 3-candidate election has a strict Condorcet winner equals the probability that it has both a strict Condorcet winner and a strict Condorcet loser.
-/

def condorcet_three_winner_prob_eq_both_prob_beats {k : ℕ} (P : Fin k → Equiv.Perm (Fin 3)) (x y : Fin 3) : Prop :=
  (Finset.filter (fun v => P v x < P v y) Finset.univ).card >
  (Finset.filter (fun v => P v y < P v x) Finset.univ).card

lemma condorcet_three_winner_prob_eq_both_prob_sum_cards_eq_k (k : ℕ) (P : Fin k → Equiv.Perm (Fin 3)) (x y : Fin 3) (hxy : x ≠ y) :
    (Finset.filter (fun v => P v x < P v y) Finset.univ).card +
    (Finset.filter (fun v => P v y < P v x) Finset.univ).card = k := by
  have h_disj : Disjoint (Finset.filter (fun v => P v x < P v y) Finset.univ)
                         (Finset.filter (fun v => P v y < P v x) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    exact lt_asymm h1 h2
  have h_union : Finset.filter (fun v => P v x < P v y) Finset.univ ∪
                 Finset.filter (fun v => P v y < P v x) Finset.univ = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have h_ne : P v x ≠ P v y := fun h => hxy ((P v).injective h)
    exact iff_of_true (lt_or_gt_of_ne h_ne) trivial
  rw [← Finset.card_union_of_disjoint h_disj, h_union]
  simp

lemma condorcet_three_winner_prob_eq_both_prob_ne_of_add_eq_odd {a b k : ℕ} (hk : Odd k) (h : a + b = k) : a ≠ b := by
  rintro rfl
  have : Even (a + a) := ⟨a, rfl⟩
  rw [h] at this
  exact Nat.not_even_iff_odd.mpr hk this

lemma condorcet_three_winner_prob_eq_both_prob_beats_or_beats {k : ℕ} (hk : Odd k) (P : Fin k → Equiv.Perm (Fin 3)) (x y : Fin 3) (hxy : x ≠ y) :
    condorcet_three_winner_prob_eq_both_prob_beats P x y ∨ condorcet_three_winner_prob_eq_both_prob_beats P y x := by
  have h_sum := condorcet_three_winner_prob_eq_both_prob_sum_cards_eq_k k P x y hxy
  have h_ne := condorcet_three_winner_prob_eq_both_prob_ne_of_add_eq_odd hk h_sum
  exact lt_or_gt_of_ne h_ne.symm

lemma condorcet_three_winner_prob_eq_both_prob_exists_loser_of_winner {k : ℕ} (hk : Odd k) (P : Fin k → Equiv.Perm (Fin 3))
    (h : ∃ w : Fin 3, condorcet_winner (fun v x y => P v x < P v y) w) :
    ∃ l : Fin 3, condorcet_loser (fun v x y => P v x < P v y) l := by
  rcases h with ⟨w, hw⟩
  fin_cases w
  · rcases condorcet_three_winner_prob_eq_both_prob_beats_or_beats hk P 1 2 (by decide) with h12 | h21
    · use 2
      intro y hy
      fin_cases y
      · exact hw 2 (by decide)
      · exact h12
      · contradiction
    · use 1
      intro y hy
      fin_cases y
      · exact hw 1 (by decide)
      · contradiction
      · exact h21
  · rcases condorcet_three_winner_prob_eq_both_prob_beats_or_beats hk P 0 2 (by decide) with h02 | h20
    · use 2
      intro y hy
      fin_cases y
      · exact h02
      · exact hw 2 (by decide)
      · contradiction
    · use 0
      intro y hy
      fin_cases y
      · contradiction
      · exact hw 0 (by decide)
      · exact h20
  · rcases condorcet_three_winner_prob_eq_both_prob_beats_or_beats hk P 0 1 (by decide) with h01 | h10
    · use 1
      intro y hy
      fin_cases y
      · exact h01
      · contradiction
      · exact hw 1 (by decide)
    · use 0
      intro y hy
      fin_cases y
      · contradiction
      · exact h10
      · exact hw 0 (by decide)

/-- For 3 candidates and odd voters, existence of a Condorcet winner implies existence of a Condorcet loser. -/
theorem condorcet_three_winner_prob_eq_both_prob (k : ℕ) (hk : Odd k) :
    impartial_culture_winner_prob k 3 = impartial_culture_winner_loser_prob k 3 := by
  have h_pred : (fun P : Fin k → Equiv.Perm (Fin 3) =>
      ∃ w : Fin 3, condorcet_winner (fun (v : Fin k) (x y : Fin 3) => P v x < P v y) w) =
    (fun P =>
      (∃ w : Fin 3, condorcet_winner (fun (v : Fin k) (x y : Fin 3) => P v x < P v y) w) ∧
      (∃ l : Fin 3, condorcet_loser (fun (v : Fin k) (x y : Fin 3) => P v x < P v y) l)) := by
    funext P
    apply propext
    constructor
    · intro hw
      exact ⟨hw, condorcet_three_winner_prob_eq_both_prob_exists_loser_of_winner hk P hw⟩
    · intro ⟨hw, _⟩
      exact hw
  change impartial_culture_prob k 3 _ = impartial_culture_prob k 3 _
  rw [h_pred]
