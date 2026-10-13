import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.TournamentExistsDecyclingFamily
import AFTD.Kb.Tcs.DigraphIsAcyclicDijoin
import AFTD.Kb.Tcs.TournamentExistsFamilyLengthEqInversionNumber

/-!
# tournament_dijoin_inversion_number_le_add

Topic: graphs   Node: 36ded5f646e0

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 ("it is easy to see that inv(D₁ → D₂) ≤ inv(D₁) + inv(D₂)").

For finite tournaments D₁, D₂: inv(D₁ → D₂) ≤ inv(D₁) + inv(D₂), by inverting an optimal family of D₁ and then one of D₂.
-/

theorem tournament_dijoin_inversion_number_le_add
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) ≤
      digraph_inversion_number D₁ + digraph_inversion_number D₂ := by
  obtain ⟨Xs, hXl, hXa⟩ := tournament_exists_family_length_eq_inversion_number V D₁ h₁
  obtain ⟨Ys, hYl, hYa⟩ := tournament_exists_family_length_eq_inversion_number W D₂ h₂
  have stepL : ∀ (E₁ : Digraph V) (E₂ : Digraph W) (X : Set V),
      digraph_invert (digraph_dijoin E₁ E₂) (Sum.inl '' X) =
        digraph_dijoin (digraph_invert E₁ X) E₂ := by
    intro E₁ E₂ X
    ext x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp [digraph_invert, digraph_dijoin]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun ha hb => h1 _ ha rfl _ hb rfl, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun x hx hxa y hy hyb => h1 (hxa ▸ hx) (hyb ▸ hy), h2⟩
  have stepR : ∀ (E₁ : Digraph V) (E₂ : Digraph W) (Y : Set W),
      digraph_invert (digraph_dijoin E₁ E₂) (Sum.inr '' Y) =
        digraph_dijoin E₁ (digraph_invert E₂ Y) := by
    intro E₁ E₂ Y
    ext x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp [digraph_invert, digraph_dijoin]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun ha hb => h1 _ ha rfl _ hb rfl, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun x hx hxa y hy hyb => h1 (hxa ▸ hx) (hyb ▸ hy), h2⟩
  have foldL : ∀ (Xs : List (Set V)) (E₁ : Digraph V) (E₂ : Digraph W),
      (Xs.map (Sum.inl '' ·)).foldl digraph_invert (digraph_dijoin E₁ E₂) =
        digraph_dijoin (Xs.foldl digraph_invert E₁) E₂ := by
    intro Xs
    induction Xs with
    | nil => intro E₁ E₂; rfl
    | cons X Xs ih => intro E₁ E₂; simp only [List.map_cons, List.foldl_cons, stepL, ih]
  have foldR : ∀ (Ys : List (Set W)) (E₁ : Digraph V) (E₂ : Digraph W),
      (Ys.map (Sum.inr '' ·)).foldl digraph_invert (digraph_dijoin E₁ E₂) =
        digraph_dijoin E₁ (Ys.foldl digraph_invert E₂) := by
    intro Ys
    induction Ys with
    | nil => intro E₁ E₂; rfl
    | cons Y Ys ih => intro E₁ E₂; simp only [List.map_cons, List.foldl_cons, stepR, ih]
  apply Nat.sInf_le
  refine ⟨Xs.map (Sum.inl '' ·) ++ Ys.map (Sum.inr '' ·), by simp [hXl, hYl], ?_⟩
  rw [List.foldl_append, foldL, foldR]
  exact digraph_is_acyclic_dijoin _ _ hXa hYa
