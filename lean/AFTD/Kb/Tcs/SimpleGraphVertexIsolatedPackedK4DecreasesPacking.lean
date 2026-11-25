import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphExternalK4PrivatePairDecreasesPacking
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_vertex_isolated_packed_k4_decreases_packing

Topic: graphs   Node: c4aebf933bd2

Provenance: helper lemma. A vertex-isolated packed-triangle reduction for the forced-K4 branch of simple_graph_triangle_cover_number_le_two_mul_packing_number.

If a maximum triangle packing contains abc vertex-disjoint from every other packing triangle, and abcx is a four-clique, then deleting the opposite edges ab and cx decreases the packing number, regardless of whether x belongs to another packing triangle.
-/

open scoped Sym2

theorem simple_graph_vertex_isolated_packed_k4_decreases_packing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hisolated : ∀ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) → Disjoint t ({a,b,c} : Finset (Fin n))) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) < simple_graph_triangle_packing_number G := by
  classical
  have hab : a ≠ b := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,c,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := c) (c := x)
    have h4 := hk4.card_eq
    omega
  have hac : a ≠ c := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := x)
    have h4 := hk4.card_eq
    omega
  have hax : a ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hbc : b ≠ c := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := x)
    have h4 := hk4.card_eq
    omega
  have hbx : b ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hcx : c ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have habx_face : G.IsNClique 3 ({a,b,x} : Finset (Fin n)) := by
    refine ⟨SimpleGraph.IsClique.subset ?_ hk4.isClique, ?_⟩
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    · simp [hab, hax, hbx]
  have card_inter : ∀ u : Finset (Fin n), u ∈ P → u ≠ ({a,b,c} : Finset (Fin n)) → (({a,b,x} : Finset (Fin n)) ∩ u).card ≤ 1 := by
    intro u huP hune
    have hd : Disjoint u ({a,b,c} : Finset (Fin n)) := hisolated u huP hune
    have hsub : (({a,b,x} : Finset (Fin n)) ∩ u) ⊆ ({x} : Finset (Fin n)) := by
      intro y hy
      rw [Finset.mem_inter] at hy
      rw [Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy.1 with rfl | rfl | rfl
      · exact absurd hy.2 (Finset.disjoint_left.mp hd.symm (by simp))
      · exact absurd hy.2 (Finset.disjoint_left.mp hd.symm (by simp))
      · rfl
    calc (({a,b,x} : Finset (Fin n)) ∩ u).card ≤ ({x} : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = 1 := by simp
  let P' : Finset (Finset (Fin n)) := insert ({a,b,x} : Finset (Fin n)) (P.erase ({a,b,c} : Finset (Fin n)))
  have hP'eq : P' = insert ({a,b,x} : Finset (Fin n)) (P.erase ({a,b,c} : Finset (Fin n))) := rfl
  have hnotmem : ({a,b,x} : Finset (Fin n)) ∉ P.erase ({a,b,c} : Finset (Fin n)) := by
    intro h
    have huP : ({a,b,x} : Finset (Fin n)) ∈ P := Finset.mem_of_mem_erase h
    have hne : ({a,b,x} : Finset (Fin n)) ≠ ({a,b,c} : Finset (Fin n)) := Finset.ne_of_mem_erase h
    have hd := hisolated ({a,b,x} : Finset (Fin n)) huP hne
    exact (Finset.disjoint_left.mp hd) (by simp : a ∈ ({a,b,x} : Finset (Fin n))) (by simp : a ∈ ({a,b,c} : Finset (Fin n)))
  have htri' : ∀ t ∈ P', G.IsNClique 3 t := by
    intro t ht
    rw [hP'eq] at ht
    rw [Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with rfl | ⟨htne, htP⟩
    · exact habx_face
    · exact htri t htP
  have hdisj' : (P' : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) := by
    intro t ht u hu htu
    have ht' : t ∈ P' := by simpa using ht
    have hu' : u ∈ P' := by simpa using hu
    rw [hP'eq] at ht' hu'
    rw [Finset.mem_insert, Finset.mem_erase] at ht' hu'
    rcases ht' with rfl | ⟨htne, htP⟩
    · rcases hu' with rfl | ⟨hune, huP⟩
      · exact absurd rfl htu
      · exact card_inter u huP hune
    · rcases hu' with rfl | ⟨hune, huP⟩
      · rw [Finset.inter_comm]; exact card_inter t htP htne
      · exact hdisj htP huP htu
  have hP'card : P'.card = P.card := by
    rw [hP'eq, Finset.card_insert_of_notMem hnotmem, Finset.card_erase_add_one hp]
  have hmax' : P'.card = simple_graph_triangle_packing_number G := by
    rw [hP'card, hmax]
  have hp' : ({a,b,x} : Finset (Fin n)) ∈ P' := by
    rw [hP'eq]; exact Finset.mem_insert_self _ _
  have hx' : c ∉ P'.biUnion id := by
    intro hc
    rw [hP'eq, Finset.mem_biUnion] at hc
    rcases hc with ⟨t, ht, hct⟩
    simp only [id] at hct
    rw [Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with rfl | ⟨htne, htP⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hct
      rcases hct with hca | hcb | hcx'
      · exact hac hca.symm
      · exact hbc hcb.symm
      · exact hcx hcx'
    · have hd := hisolated t htP htne
      exact (Finset.disjoint_left.mp hd) hct (by simp)
  have hprivate' : ∀ t ∈ P', t ≠ ({a,b,x} : Finset (Fin n)) → a ∉ t ∧ b ∉ t := by
    intro t ht htne
    rw [hP'eq] at ht
    rw [Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with rfl | ⟨htne', htP⟩
    · exact absurd rfl htne
    · have hd := hisolated t htP htne'
      exact ⟨(Finset.disjoint_left.mp hd.symm) (by simp : a ∈ ({a,b,c} : Finset (Fin n))),
             (Finset.disjoint_left.mp hd.symm) (by simp : b ∈ ({a,b,c} : Finset (Fin n)))⟩
  have hk4' : G.IsNClique 4 ({a,b,x,c} : Finset (Fin n)) := by
    have heq : ({a,b,x,c} : Finset (Fin n)) = ({a,b,c,x} : Finset (Fin n)) := by
      ext v
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hk4
  have key := simple_graph_external_k4_private_pair_decreases_packing n G P' a b x c htri' hdisj' hmax' hp' hx' hprivate' hk4'
  have hset : ({s(a,b), s(x,c)} : Set (Sym2 (Fin n))) = ({s(a,b), s(c,x)} : Set (Sym2 (Fin n))) := by
    rw [show s(x,c) = s(c,x) from Sym2.eq_swap]
  rw [hset] at key
  exact key
