import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominationNumber
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# three_token_k2n_domination_number_four_ge

Topic: graphs   Node: a3ce0461b397

Provenance: helper lemma. step towards three_token_k2n_domination_number_four

The domination number of the 3-token graph F_3(K_{2,4}) of the complete bipartite graph K_{2,4} is at least 4.
-/

instance three_token_k2n_domination_number_four_ge_decidableCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro x y
  dsimp [completeBipartiteGraph]
  infer_instance

abbrev three_token_k2n_domination_number_four_ge_V₀ := Fin 2 ⊕ Fin 4
abbrev three_token_k2n_domination_number_four_ge_G₀ :
    SimpleGraph three_token_k2n_domination_number_four_ge_V₀ :=
  completeBipartiteGraph (Fin 2) (Fin 4)
abbrev three_token_k2n_domination_number_four_ge_TG₀ :
    SimpleGraph { s : Finset three_token_k2n_domination_number_four_ge_V₀ // s.card = 3 } :=
  token_graph three_token_k2n_domination_number_four_ge_G₀ 3

instance three_token_k2n_domination_number_four_ge_decidableTGAdj :
    DecidableRel three_token_k2n_domination_number_four_ge_TG₀.Adj := by
  intro x y
  dsimp [three_token_k2n_domination_number_four_ge_TG₀, token_graph]
  infer_instance

def three_token_k2n_domination_number_four_ge_c
    (s : Finset three_token_k2n_domination_number_four_ge_V₀) : ℕ :=
  (s.filter (fun x => x.isLeft)).card

abbrev three_token_k2n_domination_number_four_ge_V_TG :=
  { s : Finset three_token_k2n_domination_number_four_ge_V₀ // s.card = 3 }

def three_token_k2n_domination_number_four_ge_X :
    Finset three_token_k2n_domination_number_four_ge_V_TG :=
  Finset.univ.filter (fun s => three_token_k2n_domination_number_four_ge_c s.val = 1)

def three_token_k2n_domination_number_four_ge_Y :
    Finset three_token_k2n_domination_number_four_ge_V_TG :=
  Finset.univ.filter (fun s => three_token_k2n_domination_number_four_ge_c s.val ≠ 1)

theorem three_token_k2n_domination_number_four_ge_X_card :
    three_token_k2n_domination_number_four_ge_X.card = 12 := by decide

theorem three_token_k2n_domination_number_four_ge_Y_card :
    three_token_k2n_domination_number_four_ge_Y.card = 8 := by decide

theorem three_token_k2n_domination_number_four_ge_deg_Y :
    ∀ y ∈ three_token_k2n_domination_number_four_ge_Y,
      (three_token_k2n_domination_number_four_ge_TG₀.neighborFinset y).card ≤ 6 := by decide

theorem three_token_k2n_domination_number_four_ge_deg_X :
    ∀ x ∈ three_token_k2n_domination_number_four_ge_X,
      (three_token_k2n_domination_number_four_ge_TG₀.neighborFinset x).card ≤ 4 := by decide

theorem three_token_k2n_domination_number_four_ge_neighbors_Y_in_X :
    ∀ y ∈ three_token_k2n_domination_number_four_ge_Y,
      ∀ v ∈ three_token_k2n_domination_number_four_ge_TG₀.neighborFinset y,
        v ∈ three_token_k2n_domination_number_four_ge_X := by decide

theorem three_token_k2n_domination_number_four_ge_neighbors_X_in_Y :
    ∀ x ∈ three_token_k2n_domination_number_four_ge_X,
      ∀ v ∈ three_token_k2n_domination_number_four_ge_TG₀.neighborFinset x,
        v ∈ three_token_k2n_domination_number_four_ge_Y := by decide

lemma three_token_k2n_domination_number_four_ge_X_sub
    (S : Finset three_token_k2n_domination_number_four_ge_V_TG)
    (hdom : simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀
      (S : Set three_token_k2n_domination_number_four_ge_V_TG)) :
    three_token_k2n_domination_number_four_ge_X ⊆
      (S ∩ three_token_k2n_domination_number_four_ge_X) ∪
        (S ∩ three_token_k2n_domination_number_four_ge_Y).biUnion
          (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u) := by
  intro x hx
  rcases hdom x with hxS | ⟨u, huS, hadj⟩
  · apply Finset.mem_union_left
    exact Finset.mem_inter.mpr ⟨hxS, hx⟩
  · apply Finset.mem_union_right
    have hu_neigh : u ∈ three_token_k2n_domination_number_four_ge_TG₀.neighborFinset x := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj.symm
    have huY : u ∈ three_token_k2n_domination_number_four_ge_Y :=
      three_token_k2n_domination_number_four_ge_neighbors_X_in_Y x hx u hu_neigh
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_inter.mpr ⟨huS, huY⟩, ?_⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj

lemma three_token_k2n_domination_number_four_ge_Y_sub
    (S : Finset three_token_k2n_domination_number_four_ge_V_TG)
    (hdom : simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀
      (S : Set three_token_k2n_domination_number_four_ge_V_TG)) :
    three_token_k2n_domination_number_four_ge_Y ⊆
      (S ∩ three_token_k2n_domination_number_four_ge_Y) ∪
        (S ∩ three_token_k2n_domination_number_four_ge_X).biUnion
          (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u) := by
  intro y hy
  rcases hdom y with hyS | ⟨u, huS, hadj⟩
  · apply Finset.mem_union_left
    exact Finset.mem_inter.mpr ⟨hyS, hy⟩
  · apply Finset.mem_union_right
    have hu_neigh : u ∈ three_token_k2n_domination_number_four_ge_TG₀.neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj.symm
    have huX : u ∈ three_token_k2n_domination_number_four_ge_X :=
      three_token_k2n_domination_number_four_ge_neighbors_Y_in_X y hy u hu_neigh
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_inter.mpr ⟨huS, huX⟩, ?_⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj

lemma three_token_k2n_domination_number_four_ge_card_le_sum_X
    (S : Finset three_token_k2n_domination_number_four_ge_V_TG)
    (hdom : simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀
      (S : Set three_token_k2n_domination_number_four_ge_V_TG)) :
    12 ≤ (S ∩ three_token_k2n_domination_number_four_ge_X).card +
      6 * (S ∩ three_token_k2n_domination_number_four_ge_Y).card := by
  have hsub := three_token_k2n_domination_number_four_ge_X_sub S hdom
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (S ∩ three_token_k2n_domination_number_four_ge_X)
    ((S ∩ three_token_k2n_domination_number_four_ge_Y).biUnion
      (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u))
  have h3 : ((S ∩ three_token_k2n_domination_number_four_ge_Y).biUnion
      (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u)).card ≤
        (S ∩ three_token_k2n_domination_number_four_ge_Y).card * 6 := by
    apply Finset.card_biUnion_le_card_mul
    intro u hu
    exact three_token_k2n_domination_number_four_ge_deg_Y u (Finset.mem_inter.mp hu).2
  rw [three_token_k2n_domination_number_four_ge_X_card] at h1
  omega

lemma three_token_k2n_domination_number_four_ge_card_le_sum_Y
    (S : Finset three_token_k2n_domination_number_four_ge_V_TG)
    (hdom : simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀
      (S : Set three_token_k2n_domination_number_four_ge_V_TG)) :
    8 ≤ 4 * (S ∩ three_token_k2n_domination_number_four_ge_X).card +
      (S ∩ three_token_k2n_domination_number_four_ge_Y).card := by
  have hsub := three_token_k2n_domination_number_four_ge_Y_sub S hdom
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (S ∩ three_token_k2n_domination_number_four_ge_Y)
    ((S ∩ three_token_k2n_domination_number_four_ge_X).biUnion
      (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u))
  have h3 : ((S ∩ three_token_k2n_domination_number_four_ge_X).biUnion
      (fun u => three_token_k2n_domination_number_four_ge_TG₀.neighborFinset u)).card ≤
        (S ∩ three_token_k2n_domination_number_four_ge_X).card * 4 := by
    apply Finset.card_biUnion_le_card_mul
    intro u hu
    exact three_token_k2n_domination_number_four_ge_deg_X u (Finset.mem_inter.mp hu).2
  rw [three_token_k2n_domination_number_four_ge_Y_card] at h1
  omega

lemma three_token_k2n_domination_number_four_ge_dom_ge_four
    (S : Finset three_token_k2n_domination_number_four_ge_V_TG)
    (hdom : simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀
      (S : Set three_token_k2n_domination_number_four_ge_V_TG)) :
    4 ≤ S.card := by
  have hd : Disjoint (S ∩ three_token_k2n_domination_number_four_ge_X)
      (S ∩ three_token_k2n_domination_number_four_ge_Y) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_inter, three_token_k2n_domination_number_four_ge_X,
      three_token_k2n_domination_number_four_ge_Y, Finset.mem_filter] at ha hb
    rintro rfl
    exact hb.2.2 ha.2.2
  have hu : S = (S ∩ three_token_k2n_domination_number_four_ge_X) ∪
      (S ∩ three_token_k2n_domination_number_four_ge_Y) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_inter, three_token_k2n_domination_number_four_ge_X,
      three_token_k2n_domination_number_four_ge_Y, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hcard : S.card = (S ∩ three_token_k2n_domination_number_four_ge_X).card +
      (S ∩ three_token_k2n_domination_number_four_ge_Y).card := by
    conv_lhs => rw [hu]
    exact Finset.card_union_of_disjoint hd
  have hX := three_token_k2n_domination_number_four_ge_card_le_sum_X S hdom
  have hY := three_token_k2n_domination_number_four_ge_card_le_sum_Y S hdom
  omega

/-- The domination number of the 3-token graph F_3(K_{2,4}) is at least 4. -/
theorem three_token_k2n_domination_number_four_ge :
    4 ≤ simple_graph_domination_number (token_graph (completeBipartiteGraph (Fin 2) (Fin 4)) 3) := by
  unfold simple_graph_domination_number
  have hne : {k | ∃ S : Finset three_token_k2n_domination_number_four_ge_V_TG,
      simple_graph_is_dominating three_token_k2n_domination_number_four_ge_TG₀ ↑S ∧ S.card = k}.Nonempty := by
    use (Finset.univ : Finset three_token_k2n_domination_number_four_ge_V_TG).card
    refine ⟨Finset.univ, ?_, rfl⟩
    intro v
    left
    simp
  have hmem := Nat.sInf_mem hne
  dsimp at hmem
  rcases hmem with ⟨S, hdom, hcard⟩
  rw [← hcard]
  exact three_token_k2n_domination_number_four_ge_dom_ge_four S hdom
