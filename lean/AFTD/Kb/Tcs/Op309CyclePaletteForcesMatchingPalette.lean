import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_cycle_palette_forces_matching_palette

Topic: graphs   Node: 704fe7b7269f

Provenance: helper lemma. Structural palette reduction for OP-309, motivated by the cycle/chord construction of https://arxiv.org/abs/2611.24297 and experiments 34685, 34692, 34700.

For a rich-neighbor five-coloring with the displayed edge partition, if every matching edge has four distinct cycle neighbors and every adjacent cycle edge has two other distinct cycle neighbors, then a three-color cycle forces every matching edge to use one of the other two colors.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem op309_rich_edge_forces_outside_color
    {V : Type*} (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5))
    (e a b f : G.edgeSet)
    (hea : G.lineGraph.Adj e a) (heb : G.lineGraph.Adj e b) (hef : G.lineGraph.Adj e f)
    (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    (hr : simple_graph_edge_is_rich G c e)
    (he : (c e).val < 3) (ha : (c a).val < 3) (hb : (c b).val < 3) :
    3 ≤ (c f).val := by
  have hval {x y : G.edgeSet} (h : c x ≠ c y) : (c x).val ≠ (c y).val := by
    intro heq
    exact h (Fin.ext heq)
  have hea' := hval (c.valid hea)
  have heb' := hval (c.valid heb)
  have hef' := hval (c.valid hef)
  have hab' := hval (hr a b hea heb hab)
  have haf' := hval (hr a f hea hef haf)
  have hbf' := hval (hr b f heb hef hbf)
  omega

theorem op309_four_cycle_neighbors_not_rich_local
    {V : Type*} (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5))
    (e : G.edgeSet) (x : Fin 4 → G.edgeSet)
    (hx : Function.Injective x)
    (hadj : ∀ i, G.lineGraph.Adj e (x i))
    (hcolors : ∀ i, (c (x i)).val < 3) :
    ¬ simple_graph_edge_is_rich G c e := by
  intro hr
  let q (i : Fin 4) : Fin 3 := ⟨(c (x i)).val, hcolors i⟩
  have hq : Function.Injective q := by
    intro i j heq
    by_contra hne
    have hval : c (x i) = c (x j) := by
      apply Fin.ext
      have hh := congrArg Fin.val heq
      simpa only [q] using hh
    exact (hr (x i) (x j) (hadj i) (hadj j) (fun hh => hne (hx hh))) hval
  have hc := Fintype.card_le_of_injective q hq
  norm_num at hc

theorem op309_cycle_palette_forces_matching_palette
    {V ι κ : Type*} (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5))
    (C : ι → G.edgeSet) (M : κ → G.edgeSet)
    (hcover : ∀ e, (∃ i, C i = e) ∨ (∃ a, M a = e))
    (hcycle : ∀ i, (c (C i)).val < 3)
    (hfour : ∀ a, ∃ x : Fin 4 → ι, Function.Injective (fun j => C (x j)) ∧
      ∀ j, G.lineGraph.Adj (M a) (C (x j)))
    (hlocal : ∀ i a, G.lineGraph.Adj (C i) (M a) →
      ∃ p q, C p ≠ C q ∧ C p ≠ M a ∧ C q ≠ M a ∧
        G.lineGraph.Adj (C i) (C p) ∧ G.lineGraph.Adj (C i) (C q))
    (hrn : simple_graph_is_rich_neighbor_coloring G c) :
    ∀ a, 3 ≤ (c (M a)).val := by
  have hnot (a : κ) : ¬ simple_graph_edge_is_rich G c (M a) := by
    obtain ⟨x,hx,hadj⟩ := hfour a
    exact op309_four_cycle_neighbors_not_rich_local G c (M a) (fun j => C (x j)) hx hadj (fun j => hcycle (x j))
  intro a
  obtain ⟨x,hx,hadj⟩ := hfour a
  obtain ⟨g,hg,hgrich⟩ := hrn (M a) ⟨C (x 0), hadj 0⟩
  rcases hcover g with ⟨i,hi⟩ | ⟨b,hb⟩
  · subst g
    have hcm : G.lineGraph.Adj (C i) (M a) := hg.symm
    obtain ⟨p,q,hpq,hpm,hqm,hp,hq⟩ := hlocal i a hcm
    exact op309_rich_edge_forces_outside_color G c (C i) (C p) (C q) (M a)
      hp hq hcm hpq hpm hqm hgrich (hcycle i) (hcycle p) (hcycle q)
  · subst g
    exact (hnot b hgrich).elim
