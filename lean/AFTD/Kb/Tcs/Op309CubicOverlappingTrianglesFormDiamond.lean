import AFTD.Prelude

/-!
# op309_cubic_overlapping_triangles_form_diamond

Topic: graphs   Node: 5ff41b0d7897

Provenance: helper lemma. Triangle and diamond decomposition for OP-309.

In a finite connected cubic simple graph other than K4, two triangles sharing an edge induce a diamond.
-/

theorem op309_overlap_diamond_nbrs3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u a b c : V) (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ t, G.Adj u t → t = a ∨ t = b ∨ t = c := by
  intro t ht
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hsub : ({a, b, c, t} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [G.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, t} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h3)]
    · simp [hbc, Ne.symm h2]
    · simp [hab, hac, Ne.symm h1]
  have := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree, hdeg] at this
  omega

theorem op309_cubic_overlapping_triangles_form_diamond
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdegree : ∀ v, G.degree v = 3)
    (hK4 : IsEmpty (G ≃g (⊤ : SimpleGraph (Fin 4))))
    (u v a b : V) (hdist : [u,v,a,b].Nodup)
    (huv : G.Adj u v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) : ¬ G.Adj a b := by
  intro hab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hdist
  obtain ⟨⟨huv', hua', hub'⟩, ⟨hva', hvb'⟩, hab', -⟩ := hdist
  have Nu := op309_overlap_diamond_nbrs3 G u v a b (hdegree u) huv hua hub hva' hvb' hab'
  have Nv := op309_overlap_diamond_nbrs3 G v u a b (hdegree v) huv.symm hva hvb hua' hub' hab'
  have Na := op309_overlap_diamond_nbrs3 G a u v b (hdegree a) hua.symm hva.symm hab huv' hub' hvb'
  have Nb := op309_overlap_diamond_nbrs3 G b u v a (hdegree b) hub.symm hvb.symm hab.symm huv' hua' hva'
  let S : V → Prop := fun w => w = u ∨ w = v ∨ w = a ∨ w = b
  have closed : ∀ x y, S x → G.Adj x y → S y := by
    rintro x y (rfl | rfl | rfl | rfl) hxy
    · rcases Nu y hxy with h | h | h <;> simp [S, h]
    · rcases Nv y hxy with h | h | h <;> simp [S, h]
    · rcases Na y hxy with h | h | h <;> simp [S, h]
    · rcases Nb y hxy with h | h | h <;> simp [S, h]
  have hall : ∀ w, S w := by
    intro w
    obtain ⟨p⟩ := hconn.preconnected u w
    suffices h : ∀ x y (q : G.Walk x y), S x → S y from h u w p (Or.inl rfl)
    intro x y q
    induction q with
    | nil => exact id
    | cons hadj _ ih => exact fun hx => ih (closed _ _ hx hadj)
  let f : Fin 4 → V := ![u, v, a, b]
  have finj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have fsurj : Function.Surjective f := by
    intro w
    rcases hall w with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  let e : Fin 4 ≃ V := Equiv.ofBijective f ⟨finj, fsurj⟩
  have iso : (⊤ : SimpleGraph (Fin 4)) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔ (⊤ : SimpleGraph (Fin 4)).Adj i j
        rw [SimpleGraph.top_adj]
        fin_cases i <;> fin_cases j <;>
          simp [f, huv, hua, hub, hva, hvb, hab, huv.symm, hua.symm, hub.symm, hva.symm,
            hvb.symm, hab.symm] }
  exact hK4.false iso.symm
