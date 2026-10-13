import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.TournamentExistsFamilyLengthEqInversionNumber

/-!
# digraph_inversion_number_le_of_adj_iff_reverse

Topic: graphs   Node: 5c3e57444df1

Provenance: helper lemma. Helper for the reduction in arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 4 (a set of inversions decycles D iff it decycles D̄; inv(D₂ → D₁) = inv(D̄₁ → D̄₂)).

If G's arcs are E's arcs pulled back along a map f and reversed (x → y in G iff f y → f x in E), and E is a finite tournament, then inv(G) ≤ inv(E): a decycling family of E pulls back to one of G of the same length.
-/

theorem digraph_inversion_number_le_of_adj_iff_reverse {U U' : Type} [Fintype U']
    (G : Digraph U) (E : Digraph U') (f : U → U') (hE : digraph_is_tournament E)
    (hGE : ∀ x y, G.Adj x y ↔ E.Adj (f y) (f x)) :
    digraph_inversion_number G ≤ digraph_inversion_number E := by
  obtain ⟨Zs, hZl, hZa⟩ := tournament_exists_family_length_eq_inversion_number U' E hE
  have rev : ∀ (Zs : List (Set U')) (E : Digraph U') (G : Digraph U),
      (∀ x y, G.Adj x y ↔ E.Adj (f y) (f x)) →
      ∀ x y, ((Zs.map (f ⁻¹' ·)).foldl digraph_invert G).Adj x y ↔
        (Zs.foldl digraph_invert E).Adj (f y) (f x) := by
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
  apply Nat.sInf_le
  refine ⟨Zs.map (f ⁻¹' ·), by simp [hZl], ?_⟩
  intro x hx
  apply hZa (f x)
  have hr := rev Zs E G hGE
  have key : ∀ x y, Relation.TransGen ((Zs.map (f ⁻¹' ·)).foldl digraph_invert G).Adj x y →
      Relation.TransGen (Zs.foldl digraph_invert E).Adj (f y) (f x) := by
    intro x y hxy
    induction hxy with
    | single h => exact .single ((hr _ _).1 h)
    | tail _ h ih => exact .head ((hr _ _).1 h) ih
  exact key x x hx
