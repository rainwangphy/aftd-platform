import AFTD.Prelude
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309GraphFourDegenerate
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort
import AFTD.Kb.Tcs.G

/-!
# op309_padded_port_four_degenerate_iff_five_colors

Topic: graphs   Node: ce78c8a30000

Provenance: helper lemma. OP-309 padded port-class selection, IN-1099.

For any fixed selected edge set, a valid port map to a finite four-degenerate target exists if and only if a valid port map exists directly to the complete five-vertex graph.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem in1099_port_valid_hom {V W W' : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset G.edgeSet) (Q : SimpleGraph W) (Q' : SimpleGraph W')
    (q : Sum G.edgeSet (V × Fin 3) → W) (f : Q →g Q')
    (h : op309_padded_almost_star_port_graph_valid G R Q q) :
    op309_padded_almost_star_port_graph_valid G R Q' (fun x => f (q x)) := by
  have hp : ∀ l : List W, l.Pairwise Q.Adj → (l.map f).Pairwise Q'.Adj := by
    intro l hl
    apply List.pairwise_map.mpr
    exact hl.imp (fun hab => f.map_rel hab)
  rcases h with ⟨hu, h3, h4, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv e e' he he' hve hve' hne
    exact f.map_rel (hu v hv e e' he he' hve hve' hne)
  · intro a b c hn hab hbc ha hb hc ea ea' eb ec ec' hea hea' hne heb hec hec' hne'
    obtain ⟨hEq, hclique⟩ := h3 a b c hn hab hbc ha hb hc ea ea' eb ec ec' hea hea' hne heb hec hec' hne'
    constructor
    · rcases hEq with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
    · simpa using hp [q eb, q ea, q ea'] hclique
  · intro a b c d hn hab hbc hcd ha hb hc hd ea ea' eb ec ed ed' hea hea' hne heb hec hed hed' hne'
    obtain ⟨x,y,hx,hy,hclique⟩ := h4 a b c d hn hab hbc hcd ha hb hc hd ea ea' eb ec ed ed' hea hea' hne heb hec hed hed' hne'
    refine ⟨x,y,?_,?_,?_⟩
    · simpa only [apply_ite] using congrArg f hx
    · simpa only [apply_ite] using congrArg f hy
    · simpa only [List.map_cons, List.map_nil, apply_ite] using
        hp [q eb, q ec, q (if x then ea' else ea), q (if y then ed' else ed)] hclique
  · intro x a b d hn hxa hxb hxd hx ha hb hd ea ea' eb eb' ed ed' hea hea' hne heb heb' hne' hed hed' hne''
    obtain ⟨h₁,h₂,h₃⟩ := hs x a b d hn hxa hxb hxd hx ha hb hd ea ea' eb eb' ed ed' hea hea' hne heb heb' hne' hed hed' hne''
    refine ⟨?_,?_,f.map_rel h₃⟩
    · rcases h₁ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩
    · rcases h₂ with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl ⟨congrArg f h₁, congrArg f h₂⟩
      · exact Or.inr ⟨congrArg f h₁, congrArg f h₂⟩


theorem in1099_complete_five_four_degenerate :
    op309_graph_four_degenerate (⊤ : SimpleGraph (Fin 5)) := by
  intro S hS
  obtain ⟨v, hv⟩ := hS
  refine ⟨v, hv, Finset.univ.erase v, ?_, ?_⟩
  · simp
  · intro w hw hadj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm hadj


theorem in1099_greedy {W : Type*} [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) (hQ : op309_graph_four_degenerate Q) :
    Nonempty (Q.Coloring (Fin 5)) := by
  classical
  have hpart : ∀ S : Finset W, ∃ c : W → Fin 5,
      ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → c u ≠ c v := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · obtain ⟨v, hv, T, hT, hcover⟩ := hQ S hs
        obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
        have hcard : (T.image c).card < (Finset.univ : Finset (Fin 5)).card := by
          have hi := Finset.card_image_le (s := T) (f := c)
          simp only [Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨color, _, hcolor⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        refine ⟨Function.update c v color, ?_⟩
        intro a ha b hb hab
        by_cases h1 : a = v
        · subst a
          have hne : b ≠ v := by
            intro h
            subst b
            exact Q.loopless.irrefl v hab
          have hbT := hcover b hb hab
          have hnot : c b ≠ color := by
            intro h
            apply hcolor
            exact Finset.mem_image.mpr ⟨b, hbT, h⟩
          simpa [Function.update, hne, Ne.symm hne] using hnot.symm
        · by_cases h2 : b = v
          · subst b
            have haT := hcover a ha hab.symm
            have hnot : c a ≠ color := by
              intro h
              apply hcolor
              exact Finset.mem_image.mpr ⟨a, haT, h⟩
            simpa [Function.update, h1, Ne.symm h1] using hnot
          · have ha' : a ∈ S.erase v := Finset.mem_erase.mpr ⟨h1,ha⟩
            have hb' : b ∈ S.erase v := Finset.mem_erase.mpr ⟨h2,hb⟩
            simpa [Function.update, h1, h2, Ne.symm h1, Ne.symm h2] using hc a ha' b hb' hab
      · refine ⟨fun _ => 0, ?_⟩
        intro a ha
        exact (hs ⟨a,ha⟩).elim
  obtain ⟨c,hc⟩ := hpart Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c (fun hab => hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) hab)⟩

theorem op309_padded_port_four_degenerate_iff_five_colors{V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset G.edgeSet) :
    (∃ (n : ℕ) (Q : SimpleGraph (Fin n))
      (q : Sum G.edgeSet (V × Fin 3) → Fin n),
      op309_padded_almost_star_port_graph_valid G R Q q ∧
      op309_graph_four_degenerate Q) ↔
    (∃ q : Sum G.edgeSet (V × Fin 3) → Fin 5,
      op309_padded_almost_star_port_graph_valid G R ⊤ q) := by
  constructor
  · rintro ⟨n,Q,q,h,hQ⟩
    obtain ⟨c⟩ := in1099_greedy Q hQ
    exact ⟨fun x => c (q x), in1099_port_valid_hom G R Q ⊤ q c h⟩
  · rintro ⟨q,h⟩
    exact ⟨5,⊤,q,h,in1099_complete_five_four_degenerate⟩
