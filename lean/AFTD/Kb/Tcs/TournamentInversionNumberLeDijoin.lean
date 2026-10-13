import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.TournamentExistsDecyclingFamily
import AFTD.Kb.Tcs.DigraphDijoinIsTournament
import AFTD.Kb.Tcs.TournamentExistsFamilyLengthEqInversionNumber

/-!
# tournament_inversion_number_le_dijoin

Topic: graphs   Node: deb2ccc57c05

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 ("the trivial lower bound inv(D₁ → D₂) ≥ max(inv(D₁), inv(D₂)) always holds").

For finite tournaments D₁, D₂: inv(D₁ → D₂) ≥ max(inv(D₁), inv(D₂)), since D₁ and D₂ are induced subtournaments of the dijoin and a decycling family restricts to one.
-/

theorem tournament_inversion_number_le_dijoin
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    max (digraph_inversion_number D₁) (digraph_inversion_number D₂) ≤
      digraph_inversion_number (digraph_dijoin D₁ D₂) := by
  obtain ⟨Zs, hZl, hZa⟩ := tournament_exists_family_length_eq_inversion_number (V ⊕ W)
    (digraph_dijoin D₁ D₂) (digraph_dijoin_is_tournament D₁ D₂ h₁ h₂)
  -- restricting a family along an injection
  have restrict : ∀ (U : Type) (f : U → V ⊕ W) (Zs : List (Set (V ⊕ W)))
      (E : Digraph (V ⊕ W)) (D : Digraph U), (∀ a b, E.Adj (f a) (f b) ↔ D.Adj a b) →
      ∀ a b, (Zs.foldl digraph_invert E).Adj (f a) (f b) ↔
        ((Zs.map (f ⁻¹' ·)).foldl digraph_invert D).Adj a b := by
    intro U f Zs
    induction Zs with
    | nil => intro E D hED; simpa using hED
    | cons Z Zs ih =>
      intro E D hED
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      intro a b
      simp only [digraph_invert, Set.mem_preimage, hED]
  have lower : ∀ (U : Type) (f : U → V ⊕ W) (D : Digraph U),
      (∀ a b, (digraph_dijoin D₁ D₂).Adj (f a) (f b) ↔ D.Adj a b) →
      digraph_inversion_number D ≤ digraph_inversion_number (digraph_dijoin D₁ D₂) := by
    intro U f D hD
    apply Nat.sInf_le
    refine ⟨Zs.map (f ⁻¹' ·), by simp [hZl], ?_⟩
    intro a ha
    apply hZa (f a)
    have hr := restrict U f Zs _ D hD
    have key : ∀ x y, Relation.TransGen ((Zs.map (f ⁻¹' ·)).foldl digraph_invert D).Adj x y →
        Relation.TransGen (Zs.foldl digraph_invert (digraph_dijoin D₁ D₂)).Adj (f x) (f y) := by
      intro x y hxy
      induction hxy with
      | single h => exact .single ((hr _ _).2 h)
      | tail _ h ih => exact .tail ih ((hr _ _).2 h)
    exact key a a ha
  apply max_le
  · exact lower V Sum.inl D₁ (fun a b => Iff.rfl)
  · exact lower W Sum.inr D₂ (fun a b => Iff.rfl)
