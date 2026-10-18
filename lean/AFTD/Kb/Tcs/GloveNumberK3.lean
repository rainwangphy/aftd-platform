import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.GloveNumberCompleteGraphUpperBound
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.HandshakeUpdateContam

/-!
# glove_number_k3

Topic: combinatorics   Node: 3cdf1d3dcefa

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:348

The glove number of the complete graph $K_3$ is equal to 2.
-/

lemma glove_number_k3_cover (a b : Fin 1 × Bool) : b = a ∨ b = opp_glove_side a := by
  obtain ⟨⟨u, hu⟩, bb⟩ := a
  obtain ⟨⟨u', hu'⟩, bb'⟩ := b
  have hu2 : u = u' := by omega
  subst hu2
  rcases bb with _ | _ <;> rcases bb' with _ | _ <;> simp [opp_glove_side]

lemma glove_number_k3_opp_ne (a : Fin 1 × Bool) : opp_glove_side a ≠ a := by
  intro h1
  have := congrArg Prod.snd h1
  simp [opp_glove_side] at this

lemma glove_number_k3_opp_opp (a : Fin 1 × Bool) : opp_glove_side (opp_glove_side a) = a := by
  simp [opp_glove_side]

lemma glove_number_k3_clean_step {V : Type*} (a : Fin 1 × Bool) (p q : V)
    (t : Fin 1 × Bool → Set V)
    (ha : t a = {p}) (hb : t (opp_glove_side a) = {q})
    (h : Handshake V (Fin 1)) (hc : handshake_is_clean h t) :
    handshake_edge h = s(p, q) ∧
      (handshake_update_contam h t) a = {p} ∧
      (handshake_update_contam h t) (opp_glove_side a) = {q} := by
  have hoo := glove_number_k3_opp_opp a
  have hone := glove_number_k3_opp_ne a
  cases h with
  | single x b y =>
    rcases glove_number_k3_cover a b with rfl | rfl
    · obtain ⟨h1, h2⟩ := hc
      rw [ha, Set.singleton_subset_iff] at h1
      rw [hb, Set.singleton_subset_iff] at h2
      subst h1; subst h2
      exact ⟨rfl, by simp [handshake_update_contam, ha],
        by simp [handshake_update_contam, hb, hone]⟩
    · obtain ⟨h1, h2⟩ := hc
      rw [hb, Set.singleton_subset_iff] at h1
      rw [hoo, ha, Set.singleton_subset_iff] at h2
      subst h1; subst h2
      exact ⟨Sym2.eq_swap, by simp [handshake_update_contam, ha, hoo, Ne.symm hone],
        by simp [handshake_update_contam, hb]⟩
  | double x b1 b2 y =>
    exact absurd (Subsingleton.elim b1.1 b2.1) hc.1

lemma glove_number_k3_edges_eq {V : Type*} (a : Fin 1 × Bool) (p q : V) :
    ∀ (seq : List (Handshake V (Fin 1))) (t : Fin 1 × Bool → Set V),
      t a = {p} → t (opp_glove_side a) = {q} → CleanHandshakeSeq seq t →
      ∀ h ∈ seq, handshake_edge h = s(p, q) := by
  intro seq
  induction seq with
  | nil => intro t ha hb hc h hh; exact absurd hh List.not_mem_nil
  | cons hd tl ih =>
    intro t ha hb hc
    cases hc with
    | cons _ _ t' hcle hrest =>
      have hstep := glove_number_k3_clean_step a p q t ha hb hd hcle
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact hstep.1
      · exact ih (handshake_update_contam hd t) hstep.2.1 hstep.2.2 hrest h hh

lemma glove_number_k3_all_edges_same :
    ∀ seq : List (Handshake (Fin 3) (Fin 1)),
      CleanHandshakeSeq seq (fun _ => (∅ : Set (Fin 3))) →
      ∃ e : Sym2 (Fin 3), ∀ h ∈ seq, handshake_edge h = e := by
  intro seq hclean
  rcases seq with _ | ⟨hd, tl⟩
  · exact ⟨s(0, 1), by intro h hh; exact absurd hh List.not_mem_nil⟩
  · cases hclean with
    | cons _ _ _ hc hrest =>
      cases hd with
      | single x a y =>
        refine ⟨s(x, y), ?_⟩
        have hone := glove_number_k3_opp_ne a
        have ht1 : (handshake_update_contam (Handshake.single x a y)
            (fun _ => (∅ : Set (Fin 3)))) a = {x} := by
          simp [handshake_update_contam]
        have ht2 : (handshake_update_contam (Handshake.single x a y)
            (fun _ => (∅ : Set (Fin 3)))) (opp_glove_side a) = {y} := by
          simp [handshake_update_contam, hone]
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · rfl
        · exact glove_number_k3_edges_eq a x y tl _ ht1 ht2 hrest h hh
      | double x b1 b2 y =>
        exact absurd (Subsingleton.elim b1.1 b2.1) hc.1

lemma glove_number_k3_no_one :
    ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) 1 := by
  rintro ⟨seq, hclean, hcover⟩
  obtain ⟨e, he⟩ := glove_number_k3_all_edges_same seq hclean
  have hedge1 : s((0:Fin 3), (1:Fin 3)) ∈ (SimpleGraph.completeGraph (Fin 3)).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; simp
  have hedge2 : s((1:Fin 3), (2:Fin 3)) ∈ (SimpleGraph.completeGraph (Fin 3)).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; simp
  obtain ⟨h1, h1mem, h1e⟩ := hcover _ hedge1
  obtain ⟨h2, h2mem, h2e⟩ := hcover _ hedge2
  have he1 : s(0, 1) = e := by rw [← h1e, he h1 h1mem]
  have he2 : s(1, 2) = e := by rw [← h2e, he h2 h2mem]
  exact absurd (he1.trans he2.symm) (by decide)

lemma glove_number_k3_no_zero :
    ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) 0 := by
  rintro ⟨seq, hclean, hcover⟩
  have hempty : seq = [] := by
    rcases seq with _ | ⟨hd, tl⟩
    · rfl
    · exfalso
      cases hd with
      | single x a y => exact a.1.elim0
      | double x a b y => exact a.1.elim0
  have hedge1 : s((0:Fin 3), (1:Fin 3)) ∈ (SimpleGraph.completeGraph (Fin 3)).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; simp
  obtain ⟨h, hh, -⟩ := hcover _ hedge1
  rw [hempty] at hh
  exact absurd hh List.not_mem_nil

/-- The glove number of K_3 is 2. -/
theorem glove_number_k3 : glove_number (SimpleGraph.completeGraph (Fin 3)) = 2 := by
  apply le_antisymm
  · simpa using glove_number_complete_graph_upper_bound 3 (by norm_num)
  · unfold glove_number
    have h2 : has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) 2 :=
      glove_number_complete_graph_upper_bound_has_clean_seq 2
    have hmem : sInf {k : ℕ | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) k} ∈
        {k : ℕ | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) k} :=
      Nat.sInf_mem ⟨2, h2⟩
    have h0 : sInf {k : ℕ | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) k} ≠ 0 :=
      fun hc => glove_number_k3_no_zero (hc ▸ hmem)
    have h1 : sInf {k : ℕ | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin 3)) k} ≠ 1 :=
      fun hc => glove_number_k3_no_one (hc ▸ hmem)
    omega
