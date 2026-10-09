import AFTD.Prelude

/-!
# matching_two_mul_encard_le_card

Topic: graphs   Node: 8e2e41f02acb

Provenance: helper lemma. step towards graph_matching_num_two_mul_le_card

For any matching M in a finite graph G, twice its edge cardinality is at most the number of vertices.
-/

open Sym2

lemma matching_two_mul_encard_le_card_fin2_cases (a b : Fin 2) (h : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  revert a b
  decide

noncomputable def matching_two_mul_encard_le_card_f {V : Type*} {G : SimpleGraph V} (M : G.Subgraph)
    (p : Fin 2 × M.edgeSet) : V :=
  if p.1 = 0 then (Quot.out p.2.1).1 else (Quot.out p.2.1).2

lemma matching_two_mul_encard_le_card_adj {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) (e : M.edgeSet) :
    M.Adj (Quot.out e.1).1 (Quot.out e.1).2 := by
  have he := e.2
  have hq := Quot.out_eq e.1
  rwa [← hq] at he

lemma matching_two_mul_encard_le_card_mem {V : Type*} {G : SimpleGraph V} (M : G.Subgraph)
    (p : Fin 2 × M.edgeSet) : matching_two_mul_encard_le_card_f M p ∈ M.verts := by
  dsimp [matching_two_mul_encard_le_card_f]
  split_ifs
  · exact (matching_two_mul_encard_le_card_adj M p.2).fst_mem
  · exact (matching_two_mul_encard_le_card_adj M p.2).snd_mem

lemma matching_two_mul_encard_le_card_toEdge {V : Type*} {G : SimpleGraph V} {M : G.Subgraph}
    (h : M.IsMatching) (p : Fin 2 × M.edgeSet) :
    h.toEdge ⟨matching_two_mul_encard_le_card_f M p, matching_two_mul_encard_le_card_mem M p⟩ = p.2 := by
  dsimp [matching_two_mul_encard_le_card_f]
  split_ifs with h0
  · have hadj := matching_two_mul_encard_le_card_adj M p.2
    have ht := h.toEdge_eq_of_adj hadj
    apply Subtype.ext
    have ht' : ((h.toEdge ⟨(Quot.out p.2.1).1, hadj.fst_mem⟩ : M.edgeSet) : Sym2 V) =
        s((Quot.out p.2.1).1, (Quot.out p.2.1).2) := congr_arg Subtype.val ht
    exact ht'.trans (Quot.out_eq p.2.1)
  · have hadj := matching_two_mul_encard_le_card_adj M p.2
    have ht := h.toEdge_eq_of_adj hadj.symm
    apply Subtype.ext
    have ht' : ((h.toEdge ⟨(Quot.out p.2.1).2, hadj.snd_mem⟩ : M.edgeSet) : Sym2 V) =
        s((Quot.out p.2.1).2, (Quot.out p.2.1).1) := congr_arg Subtype.val ht
    have ht'' := ht'.trans Sym2.eq_swap
    exact ht''.trans (Quot.out_eq p.2.1)

theorem matching_two_mul_encard_le_card_injective {V : Type*} {G : SimpleGraph V} {M : G.Subgraph}
    (h : M.IsMatching) : Function.Injective (matching_two_mul_encard_le_card_f M) := by
  intro p1 p2 hp
  have h_edge : p1.2 = p2.2 := by
    have h_v : (⟨matching_two_mul_encard_le_card_f M p1, matching_two_mul_encard_le_card_mem M p1⟩ : M.verts) =
        ⟨matching_two_mul_encard_le_card_f M p2, matching_two_mul_encard_le_card_mem M p2⟩ :=
      Subtype.ext hp
    have h_to := congr_arg h.toEdge h_v
    rw [matching_two_mul_encard_le_card_toEdge h p1, matching_two_mul_encard_le_card_toEdge h p2] at h_to
    exact h_to
  have h_fin : p1.1 = p2.1 := by
    by_contra hne
    have hcases := matching_two_mul_encard_le_card_fin2_cases p1.1 p2.1 hne
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [matching_two_mul_encard_le_card_f] at hp
      rw [h1, h2] at hp
      rw [if_pos rfl, if_neg (by decide)] at hp
      rw [h_edge] at hp
      exact (matching_two_mul_encard_le_card_adj M p2.2).ne hp
    · dsimp [matching_two_mul_encard_le_card_f] at hp
      rw [h1, h2] at hp
      rw [if_neg (by decide), if_pos rfl] at hp
      rw [h_edge] at hp
      have hadj := matching_two_mul_encard_le_card_adj M p2.2
      exact hadj.symm.ne hp
  exact Prod.ext h_fin h_edge

/-- For any matching M in a finite graph G, twice its edge cardinality is at most the number of vertices. -/
theorem matching_two_mul_encard_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) (M : G.Subgraph)
    (h : M.IsMatching) : 2 * M.edgeSet.encard ≤ (Fintype.card V : ℕ∞) := by
  have hinj := matching_two_mul_encard_le_card_injective h
  have hcard := ENat.card_le_card_of_injective hinj
  have hprod : ENat.card (Fin 2 × M.edgeSet) = 2 * M.edgeSet.encard := by
    rw [ENat.card_prod, ENat.card_coe_set_eq]
    simp
  rw [ENat.card_eq_coe_fintype_card (α := V)] at hcard
  exact hprod ▸ hcard
