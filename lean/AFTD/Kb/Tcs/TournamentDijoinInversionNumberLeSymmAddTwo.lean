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
# tournament_dijoin_inversion_number_le_symm_add_two

Topic: graphs   Node: 6887b4241094

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 4 (remark after Conjecture 4.1: |inv(D₁ → D₂) − inv(D̄₁ → D̄₂)| ≤ 2 and inv(D₂ → D₁) = inv(D̄₁ → D̄₂)).

For finite tournaments D₁, D₂: inv(D₁ → D₂) ≤ inv(D₂ → D₁) + 2 (with D₁, D₂ swapped this gives |inv(D₁ → D₂) − inv(D₂ → D₁)| ≤ 2): invert V(D₁) and V(D₂) first, which turns D₁ → D₂ into the reverse of D₂ → D₁, and a family decycles a digraph iff it decycles its reverse.
-/

theorem tournament_dijoin_inversion_number_le_symm_add_two
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) ≤
      digraph_inversion_number (digraph_dijoin D₂ D₁) + 2 := by
  obtain ⟨Zs, hZl, hZa⟩ := tournament_exists_family_length_eq_inversion_number (W ⊕ V)
    (digraph_dijoin D₂ D₁) (digraph_dijoin_is_tournament D₂ D₁ h₂ h₁)
  -- a family transported along `f` acts on a digraph that is the reverse of the pullback
  have rev : ∀ (Zs : List (Set (W ⊕ V))) (E : Digraph (W ⊕ V)) (G : Digraph (V ⊕ W)),
      (∀ x y, G.Adj x y ↔ E.Adj (Sum.swap y) (Sum.swap x)) →
      ∀ x y, ((Zs.map (Sum.swap ⁻¹' ·)).foldl digraph_invert G).Adj x y ↔
        (Zs.foldl digraph_invert E).Adj (Sum.swap y) (Sum.swap x) := by
    intro Zs
    induction Zs with
    | nil => intro E G hGE; simpa using hGE
    | cons Z Zs ih =>
      intro E G hGE
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      intro x y
      simp only [digraph_invert, Set.mem_preimage, hGE]
      tauto
  let G : Digraph (V ⊕ W) :=
    digraph_invert (digraph_invert (digraph_dijoin D₁ D₂) (Set.range Sum.inl))
      (Set.range Sum.inr)
  have hG : ∀ x y, G.Adj x y ↔ (digraph_dijoin D₂ D₁).Adj (Sum.swap y) (Sum.swap x) := by
    intro x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp [G, digraph_invert, digraph_dijoin]
  apply Nat.sInf_le
  refine ⟨Set.range Sum.inl :: Set.range Sum.inr :: Zs.map (Sum.swap ⁻¹' ·),
    by simp [hZl], ?_⟩
  intro x hx
  simp only [List.foldl_cons] at hx
  apply hZa (Sum.swap x)
  have hr := rev Zs _ G hG
  have key : ∀ x y, Relation.TransGen ((Zs.map (Sum.swap ⁻¹' ·)).foldl digraph_invert G).Adj x y →
      Relation.TransGen (Zs.foldl digraph_invert (digraph_dijoin D₂ D₁)).Adj
        (Sum.swap y) (Sum.swap x) := by
    intro x y hxy
    induction hxy with
    | single h => exact .single ((hr _ _).1 h)
    | tail _ h ih => exact .head ((hr _ _).1 h) ih
  exact key x x hx
