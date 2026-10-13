import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclicOfRank
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.DigraphInvertIsTournament
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tournament_exists_decycling_family

Topic: graphs   Node: cd55108617ed

Provenance: helper lemma. Helper for the bounds on inversion numbers of dijoins in arXiv:2610.13798 (the inversion number of a finite tournament is well defined). Hint: fix a numbering e of V; invert the two-element set {x, y} for each arc y → x with e x < e y; each such inversion reverses exactly that arc, and the result is ordered by e (digraph_is_acyclic_of_rank).

Every finite tournament can be made acyclic by finitely many inversions (so its inversion number is attained).
-/

theorem tournament_exists_decycling_family (V : Type) [Fintype V] (D : Digraph V)
    (h : digraph_is_tournament D) :
    ∃ Xs : List (Set V), digraph_is_acyclic (Xs.foldl digraph_invert D) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let S : Digraph V → Finset (V × V) := fun D =>
    Finset.univ.filter (fun p => e p.1 < e p.2 ∧ D.Adj p.2 p.1)
  suffices H : ∀ n, ∀ D : Digraph V, digraph_is_tournament D → (S D).card = n →
      ∃ Xs : List (Set V), digraph_is_acyclic (Xs.foldl digraph_invert D) from
    H _ D h rfl
  intro n
  induction n with
  | zero =>
    intro D hD hS
    refine ⟨[], ?_⟩
    apply digraph_is_acyclic_of_rank _ (fun v => (e v : ℕ))
    intro x y hxy
    rw [Finset.card_eq_zero] at hS
    rcases lt_trichotomy (e x) (e y) with hlt | heq | hgt
    · exact hlt
    · exfalso
      have hxy' : x = y := e.injective heq
      subst hxy'
      exact hD.1 x hxy
    · exfalso
      have hmem : (y, x) ∈ S D := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hgt, hxy⟩
      rw [hS] at hmem
      simp at hmem
  | succ n ih =>
    intro D hD hS
    obtain ⟨⟨a, b⟩, hab⟩ : (S D).Nonempty := Finset.card_pos.mp (by omega)
    have hab' := hab
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hab'
    obtain ⟨hlt, hba⟩ := hab'
    have hne : a ≠ b := fun h' => by rw [h'] at hlt; exact lt_irrefl _ hlt
    have hnab : ¬ D.Adj a b := fun h' => (hD.2 a b hne).1 h' hba
    have hS' : S (digraph_invert D {a, b}) = (S D).erase (a, b) := by
      ext ⟨u, v⟩
      simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        digraph_invert, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq, Prod.mk.injEq]
      by_cases hin : (v = a ∨ v = b) ∧ (u = a ∨ u = b)
      · have hcase : ¬ (e u < e v) ∨ (u = a ∧ v = b) := by
          obtain ⟨hv | hv, hu | hu⟩ := hin <;> subst hv <;> subst hu
          · exact Or.inl (lt_irrefl _)
          · exact Or.inl (not_lt.mpr hlt.le)
          · exact Or.inr ⟨rfl, rfl⟩
          · exact Or.inl (lt_irrefl _)
        rcases hcase with hc | ⟨rfl, rfl⟩
        · constructor
          · rintro ⟨h1, _⟩; exact absurd h1 hc
          · rintro ⟨_, h1, _⟩; exact absurd h1 hc
        · constructor
          · rintro ⟨_, ⟨_, _, h1⟩ | ⟨h1, _⟩⟩
            · exact absurd h1 hnab
            · exact absurd ⟨Or.inr rfl, Or.inl rfl⟩ h1
          · rintro ⟨h1, _⟩; exact absurd ⟨rfl, rfl⟩ h1
      · have hnot : ¬ (u = a ∧ v = b) := fun ⟨h1, h2⟩ => hin ⟨Or.inr h2, Or.inl h1⟩
        constructor
        · rintro ⟨h1, ⟨h2, h3, _⟩ | ⟨_, h2⟩⟩
          · exact absurd ⟨h2, h3⟩ hin
          · exact ⟨hnot, h1, h2⟩
        · rintro ⟨_, h1, h2⟩
          exact ⟨h1, Or.inr ⟨hin, h2⟩⟩
    have hcard : (S (digraph_invert D {a, b})).card = n := by
      rw [hS', Finset.card_erase_of_mem hab, hS]; rfl
    obtain ⟨Xs, hXs⟩ := ih _ (digraph_invert_is_tournament D _ hD) hcard
    exact ⟨({a, b} : Set V) :: Xs, hXs⟩
