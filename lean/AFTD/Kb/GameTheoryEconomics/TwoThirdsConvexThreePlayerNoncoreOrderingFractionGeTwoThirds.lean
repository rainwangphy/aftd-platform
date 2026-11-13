import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTwoThirdsConvex
import AFTD.Kb.GameTheoryEconomics.NoncoreOrderingFraction
import AFTD.Kb.GameTheoryEconomics.Predecessors
import AFTD.Kb.GameTheoryEconomics.IsInCore
import AFTD.Kb.GameTheoryEconomics.MarginalVector

/-!
# two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds

Topic: general_equilibrium   Node: dd849f691b66

Provenance: helper lemma. arXiv:2611.16207, Section 2

There exists a 2/3-convex cooperative game v on 3 players (Fin 3) satisfying v(∅) = 0 for which the probability that a uniformly random player ordering produces a marginal vector outside the core is at least 2/3 (noncore_ordering_fraction v ≥ 2/3).
-/

def two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game :
    Finset (Fin 3) → ℤ
  | S => if S = {0} then 1 else if S = {1} then 0 else if S = {2} then -2
         else if S = {0,1} then 0 else if S = {0,2} then 0 else if S = {1,2} then -1 else 0

def two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game :
    Finset (Fin 3) → ℝ :=
  fun S => (two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game S : ℝ)

abbrev two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_two_thirds_convex_int
    {α : Type*} [DecidableEq α] (v : Finset α → ℤ) : Prop :=
  ∀ S₁ S₂ S₃ : Finset α, S₁ ≠ S₂ → S₁ ≠ S₃ → S₂ ≠ S₃ →
    (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃) ∨
    (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃) ∨
    (v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃)

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_cast
    {α : Type*} [DecidableEq α] {w : Finset α → ℤ}
    (h : two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_two_thirds_convex_int w) :
    is_two_thirds_convex (fun S => (w S : ℝ)) := by
  intro S₁ S₂ S₃ h1 h2 h3
  rcases h S₁ S₂ S₃ h1 h2 h3 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨by (simp only []; exact_mod_cast a), by (simp only []; exact_mod_cast b)⟩
  · exact Or.inr (Or.inl ⟨by (simp only []; exact_mod_cast a), by (simp only []; exact_mod_cast b)⟩)
  · exact Or.inr (Or.inr ⟨by (simp only []; exact_mod_cast a), by (simp only []; exact_mod_cast b)⟩)

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_two_thirds_convex :
    is_two_thirds_convex
      two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game := by
  have h : two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_two_thirds_convex_int
      two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game := by decide
  exact two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_cast h

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_v_empty :
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game ∅ = 0 := by
  have h : two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game ∅ = 0 := by
    decide
  show ((two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game ∅ : ℤ) : ℝ) = 0
  rw [h]; norm_num

abbrev two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_int
    {α : Type*} [Fintype α] (v : Finset α → ℤ) (x : α → ℤ) : Prop :=
  ∑ i, x i = v Finset.univ ∧ ∀ S : Finset α, v S ≤ ∑ i ∈ S, x i

def two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_marginal
    (e : Fin 3 ≃ Fin 3) : Fin 3 → ℤ :=
  fun i => two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game
      (insert i (predecessors e i))
    - two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game
      (predecessors e i)

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_marginal_cast
    (e : Fin 3 ≃ Fin 3) :
    marginal_vector two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e
      = fun i => (two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_marginal e i : ℝ) := by
  funext i
  simp only [marginal_vector, two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_marginal,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game]
  push_cast
  ring

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_iff (x : Fin 3 → ℤ) :
    is_in_core two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
        (fun i => (x i : ℝ))
      ↔ two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_int
        two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game x := by
  simp only [is_in_core, two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_int,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, fun S => by exact_mod_cast h2 S⟩
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, fun S => by exact_mod_cast h2 S⟩

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_bad_iff
    (e : Fin 3 ≃ Fin 3) :
    ¬ is_in_core two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
        (marginal_vector two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e)
      ↔ ¬ two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_int
        two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game
        (two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_marginal e) := by
  rw [two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_marginal_cast,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_iff]

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_point :
    ∀ e : Fin 3 ≃ Fin 3,
      (two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_int
          two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_game
          (two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_int_marginal e)
        ↔ e 1 = 2) := by decide

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_bad_point
    (e : Fin 3 ≃ Fin 3) :
    ¬ is_in_core two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
        (marginal_vector two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e)
      ↔ e 1 ≠ 2 := by
  rw [two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_bad_iff,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_core_point e]

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_count :
    (Finset.univ.filter (fun e : Fin 3 ≃ Fin 3 => e 1 ≠ 2)).card = 4 := by decide

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_filter_eq_of_iff
    {ι : Type*} (s : Finset ι) (p q : ι → Prop) (hp : DecidablePred p) (hq : DecidablePred q)
    (h : ∀ x ∈ s, p x ↔ q x) : @Finset.filter ι p hp s = @Finset.filter ι q hq s :=
  @Finset.filter_congr ι p q hp hq s h

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_card4_simple :
    (@Finset.filter (Fin 3 ≃ Fin 3)
        (fun e => ¬ is_in_core
          two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
          (marginal_vector
            two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e))
      (Classical.decPred _) Finset.univ).card = 4 := by
  rw [show (@Finset.filter (Fin 3 ≃ Fin 3)
        (fun e => ¬ is_in_core
          two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
          (marginal_vector
            two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e))
      (Classical.decPred _) Finset.univ)
      = (Finset.univ.filter (fun e : Fin 3 ≃ Fin 3 => e 1 ≠ 2)) from
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_filter_eq_of_iff _ _ _ _ _
      (fun e _ => two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_bad_point e)]
  exact two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_count

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_card4 :
    (@Finset.filter (Fin (Fintype.card (Fin 3)) ≃ Fin 3)
        (fun e => ¬ is_in_core
          two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game
          (marginal_vector
            two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game e))
      (Classical.decPred _) Finset.univ).card = 4 :=
  two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_card4_simple

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_noncore_apply
    {α : Type*} [DecidableEq α] [Fintype α] (v : Finset α → ℝ) :
    noncore_ordering_fraction v
      = ((@Finset.filter (Fin (Fintype.card α) ≃ α) (fun e => ¬ is_in_core v (marginal_vector v e))
          (Classical.decPred _) Finset.univ).card : ℝ) / (Fintype.card α).factorial := rfl

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_noncore_eq_of_card
    {α : Type*} [DecidableEq α] [Fintype α] (v : Finset α → ℝ) (n : ℕ)
    (h : (@Finset.filter (Fin (Fintype.card α) ≃ α) (fun e => ¬ is_in_core v (marginal_vector v e))
        (Classical.decPred _) Finset.univ).card = n) :
    noncore_ordering_fraction v = (n : ℝ) / (Fintype.card α).factorial := by
  rw [two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_noncore_apply, h]

lemma two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_fraction :
    noncore_ordering_fraction
      two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game = 2/3 := by
  rw [two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_noncore_eq_of_card _ 4
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_card4]
  norm_num [Fintype.card_fin]

/-- There exists a 2/3-convex 3-player cooperative game with noncore ordering probability at least 2/3. -/
theorem two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds :
    ∃ v : Finset (Fin 3) → ℝ,
      v ∅ = 0 ∧
      is_two_thirds_convex v ∧
      (2 / 3 : ℝ) ≤ noncore_ordering_fraction v := ⟨two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_real_game,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_v_empty,
    two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_two_thirds_convex,
    by rw [two_thirds_convex_three_player_noncore_ordering_fraction_ge_two_thirds_fraction]⟩
